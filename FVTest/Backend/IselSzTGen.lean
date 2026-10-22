import FV.Backend.Proof.IselSzTDefs
import FV.Backend.Proof.IselCovTTabData

/-!
# Generator of the typed V6c cost tables (`FV/Backend/Proof/IselSzTTab*.lean`)

Untrusted: computes, by a fixpoint over the entries of the typed value table `covTabT`
(`IselCovTTabData`), the weight (`actorW`) and the branch targets (`actorT`) every entry's rules
emit (`cRule`, `IselSzTDefs`), drops the entries without a bound (those reaching a `Call`/
`CallInd`/`JTSequence` `emit` or `gen_call_args`, used only by the hand-checked rules), and
writes the cost tables as Lean literals (`IselSzTTabData`) with leaf-wise `decide +kernel`
checks: entry chunks (`IselSzTTabC*`), the rules of `lower` on every family (`IselSzTTabS*`),
`lower_branch` on every family and the terminator rules of `lower` (`IselSzTTabB`), and their
assembly (`IselSzTTab`). Prints the per-family failures (expected: only the hand-checked rules).

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselSzTDefs
FV.Backend.Proof.IselCovTTabData`):

    lake env lean --run FVTest/Backend/IselSzTGen.lean FV/Backend/Proof
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.CovT
open Backend.Proof.Cov (NK)
open Backend.Proof.Driver (szStmtK szTermK tgStmtK tgTermK)

namespace SzTGen

def costOf (aw : TermId → List AT → Option Nat) (ctab : CTab) (ins : List AT) (t : TermId) :
    Option Nat :=
  (program.rulesOf t).foldl (fun acc r =>
    match acc, cRule program covTabT aw ctab aext actor apre aOracle ins r with
    | some a, some c => some (max a c)
    | _, _ => none) (some 0)

/-- One round: recompute every entry's cost with the current table; drop the unbounded ones. -/
def round (aw : TermId → List AT → Option Nat) (ctab : CTab) : CTab :=
  ctab.filterMap fun (t, ins, _) => (costOf aw ctab ins t).map fun c => (t, ins, c)

partial def fix (aw : TermId → List AT → Option Nat) (n : Nat) (ctab : CTab) : Nat × CTab :=
  let c' := round aw ctab
  if c' == ctab || n == 0 then (n, c') else fix aw (n - 1) c'

def handStmt : List Nat := [1031, 1032, 1033]
def handBranch : List Nat := [1034, 1035, 1036, 1140]

def stmtRules : List Rule := program.rulesOf TId.lower
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := program.rulesOf TId.lower_branch

def nFam : Nat := famTab.length

end SzTGen

open SzTGen in
def run (nm : String) (aw : TermId → List AT → Option Nat) (kS kT : Nat) : IO CTab := do
  let init : CTab := covTabT.map fun (t, ins, _) => (t, ins, 0)
  let (left, tab) := fix aw 500 init
  IO.println s!"[{nm}] covTabT {covTabT.length} entries, cost table {tab.length} (fuel left {left})"
  let dropped := covTabT.filter fun (t, ins, _) => !tab.any fun e => e.1 == t && e.2.1 == ins
  for (t, _, _) in dropped do IO.println s!"  dropped: {t} {program.termName t}"
  IO.println s!"  max entry cost {tab.foldl (fun m e => max m e.2.2) 0}"
  for i in List.range nFam do
    let mut m := 0
    let mut bad : List Nat := []
    for r in stmtRules do
      match cRule program covTabT aw tab aext actor apre aOracle [.inst [i]] r with
      | some c => m := max m c; if c > kS then bad := bad ++ [r.id]
      | none => bad := bad ++ [r.id]
    let mut mb := 0
    let mut badb : List Nat := []
    for r in branchRules do
      match cRule program covTabT aw tab aext actor apre aOracle [.inst [i], .c0] r with
      | some c => mb := max mb c; if c > kT then badb := badb ++ [r.id]
      | none => badb := badb ++ [r.id]
    IO.println s!"  family {i}: stmt max {m} fail {bad}; branch max {mb} fail {badb}"
  for r in termRules do
    IO.println s!"  term {r.id}: {cRule program covTabT aw tab aext actor apre aOracle [.c0] r}"
  pure tab


namespace SzTGen

def ctyLit : CTy → String
  | .invalid => ".invalid" | .int n => s!"(.int {n})" | .float n => s!"(.float {n})"
  | .vec a b c => s!"(.vec {a} {b} {c})"

def szLit : OperandSize → String | .size32 => ".size32" | .size64 => ".size64"

def nkLit : NK → String
  | .int => "int" | .imm12 => "imm12" | .immShift => "immShift" | .uimm5 => "uimm5"
  | .uimm6 => "uimm6" | .shiftAmt => "shiftAmt" | .mwc => "mwc" | .callInfo => "callInfo"

partial def awLit : AT → String
  | .bot => ".bot" | .flat m c => s!"(.flat {m} {c})" | .reg m => s!"(.reg {m})"
  | .ty ts => s!"(.ty [{", ".intercalate (ts.map ctyLit)}])"
  | .bool b => s!"(.bool {b})" | .logic s => s!"(.logic {szLit s})" | .scale b => s!"(.scale {b})"
  | .simm9 => ".simm9"
  | .val ts => s!"(.val [{", ".intercalate (ts.map ctyLit)}])"
  | .vals tss => s!"(.vals [{", ".intercalate (tss.map fun ts => s!"[{", ".intercalate (ts.map ctyLit)}]")}])"
  | .valsAll ts => s!"(.valsAll [{", ".intercalate (ts.map ctyLit)}])"
  | .inst fs => s!"(.inst {fs})"
  | .movi => ".movi" | .extv => ".extv"
  | .alts as => s!"(.alts [{", ".intercalate (as.map awLit)}])"
  | .data t k fs => s!"(.data {t} {k} [{", ".intercalate (fs.map awLit)}])"
  | .num k b => s!"(.num .{nkLit k} {b})"

def entryLit (e : TermId × List AT × Nat) : String :=
  s!"({e.1}, [{", ".intercalate (e.2.1.map awLit)}], {e.2.2})"

def ruleNames (src : String) (t : Nat) : List String :=
  match src.splitOn s!"theorem program_rulesOf_{t} : program.rulesOf {t} =" with
  | _ :: rest :: _ =>
    let line := ((rest.splitOn "\n").getD 1 "").trimAscii.toString
    let line := ((line.splitOn " := rfl").headD line).trimAscii.toString
    let line := String.ofList ((line.toList.drop 1).dropLast)
    (line.splitOn ", ").map (·.trimAscii.toString)
  | _ => []

def groups {α : Type} (n : Nat) (l : List α) : List (List α) :=
  (List.range ((l.length + n - 1) / n)).map fun k => (l.drop (k * n)).take n

/-- Entries per chunk of a cost table; chunks per module; rules per module. -/
def chunk : Nat := 88
def chunksPerMod : Nat := 2
def rulesPerMod : Nat := 10

def preamble (title doc imports : String) : String :=
  imports ++ "\n/-!\n# The size of the ISLE lowering's output over float-capable contexts (typed V6c): " ++
  title ++ "\n\n" ++
  "GENERATED by `FVTest/Backend/IselSzTGen.lean` (untrusted; regenerate with\n" ++
  "`lake env lean --run FVTest/Backend/IselSzTGen.lean FV/Backend/Proof`). Do not edit by hand.\n\n" ++
  doc ++ "\n-/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\nset_option Elab.async false\n\n" ++
  "namespace Backend.Proof.CovT\n\nopen Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64\n\n"

def okDefs : String := "/-- `chkCost`'s test of one entry of `szCTabT`. -/
abbrev szEntryOkT (e : TermId × List AT × Nat) : Bool :=
  (program.rulesOf e.1).all (cRuleLe program covTabT actorW szCTabT aext actor apre aOracle e.2.1 e.2.2)

/-- `chkCost`'s test of one entry of `tgCTabT`. -/
abbrev tgEntryOkT (e : TermId × List AT × Nat) : Bool :=
  (program.rulesOf e.1).all (cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle e.2.1 e.2.2)

/-- The weight test of one rule of `lower`: a `call` rule (1031-1033, by hand), or on every
family at most `szStmtK`. -/
def szStmtOkT (r : Rule) : Bool :=
  r.id == 1031 || r.id == 1032 || r.id == 1033 ||
    (List.range famTab.length).all fun i =>
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.inst [i]] szStmtK r

/-- The target test of one rule of `lower`: on every family at most `tgStmtK`. -/
def tgStmtOkT (r : Rule) : Bool :=
  (List.range famTab.length).all fun i =>
    cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.inst [i]] tgStmtK r

/-- The weight test of one rule of `lower_branch`: a `try_call` or `br_table` rule (1034-1036,
1140, by hand), or on every family at most `szTermK`. -/
def szBranchOkT (r : Rule) : Bool :=
  r.id == 1034 || r.id == 1035 || r.id == 1036 || r.id == 1140 ||
    (List.range famTab.length).all fun i =>
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.inst [i], .c0] szTermK r

/-- The target test of one rule of `lower_branch`: the `br_table` rule (1140, by hand), or on
every family at most `tgTermK`. -/
def tgBranchOkT (r : Rule) : Bool :=
  r.id == 1140 ||
    (List.range famTab.length).all fun i =>
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.inst [i], .c0] tgTermK r

"

def renderTab (nm : String) (tab : CTab) : String := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut d := ""
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    d := d ++ s!"/-- Chunk {k} of the cost table `{nm}`. -/\ndef {nm}{k} : CTab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  d := d ++ s!"/-- **The cost table `{nm}`.** -/\ndef {nm} : CTab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"{nm}{·}")) ++ "\n\n"
  d

def chunkThm (nm ok : String) (k : Nat) : String :=
  s!"theorem {nm}{k}_ok : ({nm}{k}).all {ok} = true := by\n  simp only [{nm}{k}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"


/-- Rule/family pairs whose single kernel check is too large (rule 2267 on family 8 has 256
environments, `IselCovTGen.heavy`): checked chunk-wise (`IselSzTChunk.cRuleLe_of_chunks`). -/
def heavy : List (String × Nat) := [("rule_lower_2267", 8)]
def envChunk : Nat := 16

/-- The parameters of a chunked check: the if-lets' and the right-hand sides' maximum costs and
the chunk counts. -/
structure HeavyP where
  a : Nat
  b : Nat
  nA : Nat
  nB : Nat

def heavyP (aw : TermId → List AT → Option Nat) (ctab : CTab) (i : Nat) (r : Rule) : HeavyP :=
  let pats := aPatArgs program aext [.inst [i]] r.args (List.replicate r.vars.length .top)
  let a := pats.foldl (fun m e => max m ((cIfLets program covTabT aw ctab aext actor apre aOracle r.iflets e).getD 0)) 0
  let envs := (aRuleEnvs program covTabT aext actor apre aOracle [.inst [i]] r).getD []
  let b := envs.foldl (fun m e => max m ((cExpr program covTabT aw ctab actor apre aOracle r.rhs e).getD 0)) 0
  ⟨a, b, (pats.length + envChunk - 1) / envChunk, (envs.length + envChunk - 1) / envChunk⟩

/-- The chunked check of heavy rule `r` on family `i` for one of the two analyses. -/
def heavyThm (kind : String) (r : String) (i : Nat) (hp : HeavyP) : String := Id.run do
  let (aw, tab, bound, okName) :=
    if kind == "sz" then ("actorW", "szCTabT", "szStmtK", "szStmtOkT") else ("actorT", "tgCTabT", "tgStmtK", "tgStmtOkT")
  let k := envChunk
  let pats := s!"(aPatArgs program aext [.inst [{i}]] {r}.args (List.replicate {r}.vars.length .top))"
  let envs := s!"(aRuleEnvs program covTabT aext actor apre aOracle [.inst [{i}]] {r})"
  let pre := s!"{okName}_{r}_f{i}"
  let mut s := s!"theorem {pre}_nA : {pats}.length ≤ {hp.nA} * {k} := by decide +kernel\n\n"
  for c in List.range hp.nA do
    s := s ++ s!"theorem {pre}_A{c} : (({pats}.drop ({c} * {k})).take {k}).all\n    (ifOk program covTabT {aw} {tab} aext actor apre aOracle {r} {hp.a}) = true := by decide +kernel\n\n"
  s := s ++ s!"theorem {pre}_s : {envs}.isSome = true := by decide +kernel\n\n"
  s := s ++ s!"theorem {pre}_nB : ({envs}.getD []).length ≤ {hp.nB} * {k} := by decide +kernel\n\n"
  for c in List.range hp.nB do
    s := s ++ s!"theorem {pre}_B{c} : ((({envs}.getD []).drop ({c} * {k})).take {k}).all\n    (envOk program covTabT {aw} {tab} actor apre aOracle {r} {hp.b}) = true := by decide +kernel\n\n"
  s := s ++ s!"theorem {okName}_{r}_rest : (List.range famTab.length).all (fun i => i == {i} ||\n    cRuleLe program covTabT {aw} {tab} aext actor apre aOracle [.inst [i]] {bound} {r}) = true := by\n  decide +kernel\n\n"
  let hid := if kind == "sz" then "  simp only [Bool.or_eq_true]\n  right\n" else ""
  s := s ++ s!"theorem {okName}_{r} : {okName} {r} = true := by\n  unfold {okName}\n{hid}  rw [List.all_eq_true]\n  intro i hi\n  by_cases hi' : i = {i}\n  · subst hi'\n    refine cRuleLe_of_chunks {hp.a} {hp.b} {k} {hp.nA} {k} {hp.nB} (by decide) {pre}_nA ?_ {pre}_s {pre}_nB ?_\n    · intro c hc\n      match c, hc with\n"
  for c in List.range hp.nA do
    s := s ++ s!"      | {c}, _ => exact {pre}_A{c}\n"
  s := s ++ s!"      | _ + {hp.nA}, hc => exact absurd hc (by omega)\n    · intro c hc\n      match c, hc with\n"
  for c in List.range hp.nB do
    s := s ++ s!"      | {c}, _ => exact {pre}_B{c}\n"
  s := s ++ s!"      | _ + {hp.nB}, hc => exact absurd hc (by omega)\n  · have := List.all_eq_true.1 {okName}_{r}_rest i hi\n    simpa [hi'] using this\n\n"
  s

def renderAll (sz tg : CTab) (lowerNames branchNames : List String)
    (heavyN : List (String × Nat × HeavyP × HeavyP)) : List (String × String) := Id.run do
  let nS := (sz.length + chunk - 1) / chunk
  let nT := (tg.length + chunk - 1) / chunk
  let mut files : List (String × String) := []
  let mut d := preamble "the cost tables"
    "`szCTabT`/`tgCTabT`: per entry of the typed value table `covTabT` whose rules have a bound, the
weight (`actorW`) and the branch targets (`actorT`) they emit. The leaf-wise kernel checks are in
`IselSzTTabC*` (entries), `IselSzTTabS*` (the rules of `lower` on every family), `IselSzTTabB`
(`lower_branch` on every family, the terminator rules of `lower`); `IselSzTTab` assembles them."
    "import FV.Backend.Proof.IselSzTDefs\nimport FV.Backend.Proof.IselCovTTabData\n"
  d := d ++ renderTab "szCTabT" sz ++ renderTab "tgCTabT" tg ++ okDefs ++ "end Backend.Proof.CovT\n"
  files := files ++ [("IselSzTTabData.lean", d)]
  let jobs : List (String × String × Nat) :=
    ((List.range nS).map fun k => ("szCTabT", "szEntryOkT", k)) ++
      ((List.range nT).map fun k => ("tgCTabT", "tgEntryOkT", k))
  let cgs := groups chunksPerMod jobs
  for (js, gi) in cgs.zipIdx do
    let mut c := preamble s!"cost table entries, group {gi}" "Every rule of every entry of these chunks is within the entry's bound." "import FV.Backend.Proof.IselSzTTabData\n"
    for (nm, ok, k) in js do
      c := c ++ chunkThm nm ok k
    files := files ++ [(s!"IselSzTTabC{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  let sgs := groups rulesPerMod lowerNames
  for (rs, gi) in sgs.zipIdx do
    let isHeavy := rs.any (fun r => heavyN.any (·.1 == r))
    let imp := if isHeavy then "import FV.Backend.Proof.IselSzTTabData\nimport FV.Backend.Proof.IselSzTChunk\n" else "import FV.Backend.Proof.IselSzTTabData\n"
    let mut c := preamble s!"rules of `lower`, group {gi}" "Each rule of `lower` is within `szStmtK`/`tgStmtK` on every family (`szStmtOkT`, `tgStmtOkT`)." imp
    for r in rs do
      match heavyN.find? (·.1 == r) with
      | some (_, i, hs, ht) =>
        c := c ++ heavyThm "sz" r i hs ++ heavyThm "tg" r i ht
      | none =>
        c := c ++ s!"theorem szStmtOkT_{r} : szStmtOkT {r} = true := by decide +kernel\n\n"
        c := c ++ s!"theorem tgStmtOkT_{r} : tgStmtOkT {r} = true := by decide +kernel\n\n"
    files := files ++ [(s!"IselSzTTabS{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  let mut bc := preamble "rules of `lower_branch`, terminators" "Each rule of `lower_branch` is within `szTermK`/`tgTermK` on every family (`szBranchOkT`, `tgBranchOkT`); the terminator rules of `lower` (964 `trap`, 1037 `return`) on `c0`." "import FV.Backend.Proof.IselSzTTabData\n"
  for r in branchNames do
    bc := bc ++ s!"theorem szBranchOkT_{r} : szBranchOkT {r} = true := by decide +kernel\n\n"
    bc := bc ++ s!"theorem tgBranchOkT_{r} : tgBranchOkT {r} = true := by decide +kernel\n\n"
  bc := bc ++ "/-- The terminator rules of `lower` (964 `trap`, 1037 `return`) emit at most `szTermK`. -/
theorem szTermT_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.c0] szTermK r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

/-- The terminator rules of `lower` (964 `trap`, 1037 `return`) emit at most `tgTermK` branch
targets. -/
theorem tgTermT_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.c0] tgTermK r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

"
  files := files ++ [("IselSzTTabB.lean", bc ++ "end Backend.Proof.CovT\n")]
  let imps := "import FV.Backend.Proof.IselSzTTabB\n" ++
    String.join ((List.range cgs.length).map (s!"import FV.Backend.Proof.IselSzTTabC{·}\n")) ++
    String.join ((List.range sgs.length).map (s!"import FV.Backend.Proof.IselSzTTabS{·}\n"))
  let mut m := preamble "the cost tables and root checks"
    "`szCTabT_ok`/`tgCTabT_ok`: every rule of every entry is within the entry's bound (`chkCost`);
`szStmtT_ok`/`tgStmtT_ok`: every rule of `lower` on every family (but the hand-checked `call`
rules' weight); `szBranchT_ok`/`tgBranchT_ok`: every rule of `lower_branch` on every family (but
the hand-checked `try_call` and `br_table` rules); `szTermT_ok`/`tgTermT_ok` (`IselSzTTabB`): the
terminator rules of `lower`."
    imps
  m := m ++ "/-- **Every rule of every entry of `szCTabT` checks.** -/\ntheorem szCTabT_ok : chkCost program covTabT actorW szCTabT aext actor apre aOracle = true := by\n  unfold chkCost\n  show (szCTabT).all szEntryOkT = true\n  simp only [szCTabT, List.all_append, " ++
    ", ".intercalate ((List.range nS).map (s!"szCTabT{·}_ok")) ++ ", Bool.and_self]\n\n"
  m := m ++ "/-- **Every rule of every entry of `tgCTabT` checks.** -/\ntheorem tgCTabT_ok : chkCost program covTabT actorT tgCTabT aext actor apre aOracle = true := by\n  unfold chkCost\n  show (tgCTabT).all tgEntryOkT = true\n  simp only [tgCTabT, List.all_append, " ++
    ", ".intercalate ((List.range nT).map (s!"tgCTabT{·}_ok")) ++ ", Bool.and_self]\n\n"
  for (nm, names) in [("szStmtOkT", lowerNames), ("tgStmtOkT", lowerNames)] do
    let thm := if nm == "szStmtOkT" then "szStmtT_ok" else "tgStmtT_ok"
    m := m ++ s!"/-- **Every rule of `lower` passes `{nm}`.** -/\ntheorem {thm} : (program.rulesOf TId.lower).all {nm} = true := by\n  rw [show TId.lower = 686 from rfl, program_rulesOf_686]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
      ", ".intercalate (names.map (s!"{nm}_{·}")) ++ "]\n\n"
  for (nm, names) in [("szBranchOkT", branchNames), ("tgBranchOkT", branchNames)] do
    let thm := if nm == "szBranchOkT" then "szBranchT_ok" else "tgBranchT_ok"
    m := m ++ s!"/-- **Every rule of `lower_branch` passes `{nm}`.** -/\ntheorem {thm} : (program.rulesOf TId.lower_branch).all {nm} = true := by\n  rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
      ", ".intercalate (names.map (s!"{nm}_{·}")) ++ "]\n\n"
  files := files ++ [("IselSzTTab.lean", m ++ "end Backend.Proof.CovT\n")]
  files

end SzTGen

open SzTGen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselSzTGen <out dir>"; return 1
  let sz ← run "weight" actorW szStmtK szTermK
  let tg ← run "targets" actorT tgStmtK tgTermK
  let src ← IO.FS.readFile "FV/Backend/Proof/IselData.lean"
  let ln := ruleNames src 686
  let bn := ruleNames src 687
  IO.println s!"lower rules {ln.length} branch rules {bn.length}"
  if ln.length != stmtRules.length || bn.length != branchRules.length then
    IO.eprintln "rule name lists do not match the program"; return 1
  let heavyN := heavy.filterMap fun (name, i) => ((ln.zip stmtRules).find? (·.1 == name)).map
    fun (_, r) => (name, i, heavyP actorW sz i r, heavyP actorT tg i r)
  for (n, i, hs, ht) in heavyN do
    IO.println s!"heavy {n} f{i}: sz a={hs.a} b={hs.b} nA={hs.nA} nB={hs.nB}; tg a={ht.a} b={ht.b} nA={ht.nA} nB={ht.nB}"
  for (name, content) in renderAll sz tg ln bn heavyN do
    IO.FS.writeFile (path ++ "/" ++ name) content
  return 0
