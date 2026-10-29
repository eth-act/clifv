module

public import FV.Backend.Proof.IselSzTDefs
public import FV.Backend.Proof.IselCovTTabData
public import FVTest.ModuleHeader

@[expose] public section

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
  doc ++ "\n-/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n" ++
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

/-- The check of chunk `k` of table `nm` (`len` entries), in sub-chunks of `sk` entries, one
kernel `decide` (and one declaration) each, assembled by `all_of_chunks`. -/
def chunkThm (nm ok : String) (k len sk : Nat) (alt : Nat → Option String := fun _ => none) :
    String := Id.run do
  let n := (len + sk - 1) / sk
  let mut s := s!"theorem {nm}{k}_len : ({nm}{k}).length ≤ {n} * {sk} := by decide +kernel\n\n"
  for c in List.range n do
    s := s ++ (alt c).getD
      s!"theorem {nm}{k}_p{c} : ((({nm}{k}).drop ({c} * {sk})).take {sk}).all {ok} = true := by\n  decide +kernel\n\n"
  s := s ++ s!"theorem {nm}{k}_ok : ({nm}{k}).all {ok} = true :=\n  all_of_chunks _ _ {sk} {n} {nm}{k}_len fun c hc => match c, hc with\n"
  for c in List.range n do
    s := s ++ s!"    | {c}, _ => {nm}{k}_p{c}\n"
  s := s ++ s!"    | _ + {n}, hc => absurd hc (by omega)\n\n"
  s

/-- The abstract environments an entry's rules go through (its kernel check's size). -/
def entryEnvs (e : TermId × List AT × Nat) : Nat :=
  (program.rulesOf e.1).foldl (fun acc r =>
    acc + ((aRuleEnvs program covTabT aext actor apre aOracle e.2.1 r).getD []).length +
      (aPatArgs program aext e.2.1 r.args (List.replicate r.vars.length .top)).length) 0

/-- Sub-chunk size: one entry per declaration (8 entries of fewer than 50 environments each took
8.1 GB in one `decide`: the environment count does not predict the kernel's cost). -/
def subChunk (_es : CTab) : Nat := 1


/-- Rule/family pairs whose single kernel check is too large (rule 2267 on family 8 has 256
environments, `IselCovTGen.heavy`): checked chunk-wise (`IselSzTChunk.cRuleLe_of_chunks`). -/
def heavy : List (String × Nat × Nat) :=
  [("rule_lower_2267", 8, 16), ("rule_lower_1222", 2, 8), ("rule_lower_1224", 2, 8),
   ("rule_lower_1226", 2, 8), ("rule_lower_1228", 2, 8)]

/-- The parameters of a chunked check: the if-lets' and the right-hand sides' maximum costs and
the chunk counts. -/
structure HeavyP where
  a : Nat
  b : Nat
  k : Nat
  nA : Nat
  nB : Nat

def heavyPI (aw : TermId → List AT → Option Nat) (ctab : CTab) (ins : List AT) (k : Nat) (r : Rule) :
    HeavyP :=
  let pats := aPatArgs program aext ins r.args (List.replicate r.vars.length .top)
  let a := pats.foldl (fun m e => max m ((cIfLets program covTabT aw ctab aext actor apre aOracle r.iflets e).getD 0)) 0
  let envs := (aRuleEnvs program covTabT aext actor apre aOracle ins r).getD []
  let b := envs.foldl (fun m e => max m ((cExpr program covTabT aw ctab actor apre aOracle r.rhs e).getD 0)) 0
  ⟨a, b, k, (pats.length + k - 1) / k, (envs.length + k - 1) / k⟩

def heavyP (aw : TermId → List AT → Option Nat) (ctab : CTab) (i k : Nat) (r : Rule) : HeavyP :=
  heavyPI aw ctab [.inst [i]] k r

/-- The chunked check of heavy rule `r` on family `i` for one of the two analyses. -/
def heavyThm (kind : String) (r : String) (i : Nat) (hp : HeavyP) : String := Id.run do
  let (aw, tab, bound, okName) :=
    if kind == "sz" then ("actorW", "szCTabT", "szStmtK", "szStmtOkT") else ("actorT", "tgCTabT", "tgStmtK", "tgStmtOkT")
  let k := hp.k
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

/-- Environments per kernel `decide` and per module in the chunked check of a heavy entry (term
575's entries go through about 4040 environments each; one `decide` per entry ran out of memory
at 9.2 GB). -/
def entryK : Nat := 128
def entryModEnvs : Nat := 1024

/-- The chunked check of heavy entry `e` (sub-chunk `c` of chunk `k` of table `nm`, `ok` its
entry test): every rule of the entry, each by one `decide` or, if it has more than `entryK`
environments, by `cRuleLe_of_chunks` from checks of `entryK` environments. Returns the
declarations for separate modules (each about `entryModEnvs` environments) and the assembly
(rule-level `cRuleLe_of_chunks` proofs and the sub-chunk theorem) for the chunk's module. -/
def heavyEntry (nm ok aw : String) (awF : TermId → List AT → Option Nat) (ctab : CTab) (k c : Nat)
    (e : TermId × List AT × Nat) (names : List String) : List String × String := Id.run do
  let pre := s!"{nm}{k}_p{c}"
  let ins := s!"[{", ".intercalate (e.2.1.map awLit)}]"
  let call := s!"cRuleLe program covTabT {aw} {nm} aext actor apre aOracle {ins} {e.2.2}"
  let mut mods : List String := []
  let mut cur := ""
  let mut curN := 0
  let mut asm := ""
  let mut push : List (Nat × String) := []
  for ((r, rn), j) in ((program.rulesOf e.1).zip names).zipIdx do
    let pats := aPatArgs program aext e.2.1 r.args (List.replicate r.vars.length .top)
    let envs := (aRuleEnvs program covTabT aext actor apre aOracle e.2.1 r).getD []
    let rp := s!"{pre}_r{j}"
    if pats.length + envs.length ≤ entryK then
      push := push ++ [(pats.length + envs.length,
        s!"theorem {rp} : {call} {rn} = true := by decide +kernel\n\n")]
    else
      let hp := heavyPI awF ctab e.2.1 entryK r
      let patsS := s!"(aPatArgs program aext {ins} {rn}.args (List.replicate {rn}.vars.length .top))"
      let envsS := s!"(aRuleEnvs program covTabT aext actor apre aOracle {ins} {rn})"
      push := push ++ [(1, s!"theorem {rp}_nA : {patsS}.length ≤ {hp.nA} * {entryK} := by decide +kernel\n\n")]
      for i in List.range hp.nA do
        push := push ++ [(entryK, s!"theorem {rp}_A{i} : (({patsS}.drop ({i} * {entryK})).take {entryK}).all\n    (ifOk program covTabT {aw} {nm} aext actor apre aOracle {rn} {hp.a}) = true := by decide +kernel\n\n")]
      push := push ++ [(1, s!"theorem {rp}_s : {envsS}.isSome = true := by decide +kernel\n\n"),
        (1, s!"theorem {rp}_nB : ({envsS}.getD []).length ≤ {hp.nB} * {entryK} := by decide +kernel\n\n")]
      for i in List.range hp.nB do
        push := push ++ [(entryK, s!"theorem {rp}_B{i} : ((({envsS}.getD []).drop ({i} * {entryK})).take {entryK}).all\n    (envOk program covTabT {aw} {nm} actor apre aOracle {rn} {hp.b}) = true := by decide +kernel\n\n")]
      asm := asm ++ s!"theorem {rp} : {call} {rn} = true := by\n  refine cRuleLe_of_chunks {hp.a} {hp.b} {entryK} {hp.nA} {entryK} {hp.nB} (by decide) {rp}_nA ?_ {rp}_s {rp}_nB ?_\n  · intro c hc\n    match c, hc with\n"
      for i in List.range hp.nA do
        asm := asm ++ s!"    | {i}, _ => exact {rp}_A{i}\n"
      asm := asm ++ s!"    | _ + {hp.nA}, hc => exact absurd hc (by omega)\n  · intro c hc\n    match c, hc with\n"
      for i in List.range hp.nB do
        asm := asm ++ s!"    | {i}, _ => exact {rp}_B{i}\n"
      asm := asm ++ s!"    | _ + {hp.nB}, hc => exact absurd hc (by omega)\n\n"
  for (n, s) in push do
    if curN + n > entryModEnvs && curN > 0 then
      mods := mods ++ [cur]; cur := ""; curN := 0
    cur := cur ++ s; curN := curN + n
  if curN > 0 then mods := mods ++ [cur]
  let thms := ", ".intercalate ((List.range names.length).map (s!"{pre}_r{·}"))
  asm := asm ++ s!"theorem {pre} : ((({nm}{k}).drop ({c} * 1)).take 1).all {ok} = true := by\n  rw [show (({nm}{k}).drop ({c} * 1)).take 1 = [{entryLit e}] from rfl]\n  simp only [List.all_cons, List.all_nil, Bool.and_true]\n  show (program.rulesOf {e.1}).all ({call}) = true\n  rw [program_rulesOf_{e.1}]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, {thms}, Bool.and_self]\n\n"
  (mods, asm)

def renderAll (src : String) (sz tg : CTab) (lowerNames branchNames : List String)
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
  let jobs : List (String × String × Nat × Nat × Nat) :=
    ((List.range nS).map fun k => let es := (sz.drop (k * chunk)).take chunk
      ("szCTabT", "szEntryOkT", k, es.length, subChunk es)) ++
    ((List.range nT).map fun k => let es := (tg.drop (k * chunk)).take chunk
      ("tgCTabT", "tgEntryOkT", k, es.length, subChunk es))
  let cgs := groups chunksPerMod jobs
  let mut hi := 0
  for (js, gi) in cgs.zipIdx do
    let mut body := ""
    let mut imps := "import FV.Backend.Proof.IselSzTTabData\nimport FV.Backend.Proof.IselSzTChunk\n"
    for (nm, ok, k, len, sk) in js do
      let (tab, aw, awF) := if nm == "szCTabT" then (sz, "actorW", actorW) else (tg, "actorT", actorT)
      let es := (tab.drop (k * chunk)).take chunk
      let mut alts : List (Nat × String) := []
      if sk == 1 then
        for (e, c) in es.zipIdx do
          if entryEnvs e > 1000 then
            let (mods, asm) := heavyEntry nm ok aw awF tab k c e (ruleNames src e.1)
            for m in mods do
              files := files ++ [(s!"IselSzTTabH{hi}.lean", preamble s!"cost table entries, heavy entry part {hi}" s!"Chunk checks of the rules of entry {c} of chunk {k} of `{nm}` (assembled in `IselSzTTabC{gi}`)." "import FV.Backend.Proof.IselSzTTabData\nimport FV.Backend.Proof.IselSzTChunk\n" ++ m ++ "end Backend.Proof.CovT\n")]
              imps := imps ++ s!"import FV.Backend.Proof.IselSzTTabH{hi}\n"
              hi := hi + 1
            alts := alts ++ [(c, asm)]
      body := body ++ chunkThm nm ok k len sk (fun c => (alts.find? (·.1 == c)).map (·.2))
    let c := preamble s!"cost table entries, group {gi}" "Every rule of every entry of these chunks is within the entry's bound." imps
    files := files ++ [(s!"IselSzTTabC{gi}.lean", c ++ body ++ "end Backend.Proof.CovT\n")]
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
  let heavyN := heavy.filterMap fun (name, i, k) => ((ln.zip stmtRules).find? (·.1 == name)).map
    fun (_, r) => (name, i, heavyP actorW sz i k r, heavyP actorT tg i k r)
  for (n, i, hs, ht) in heavyN do
    IO.println s!"heavy {n} f{i}: sz a={hs.a} b={hs.b} nA={hs.nA} nB={hs.nB}; tg a={ht.a} b={ht.b} nA={ht.nA} nB={ht.nB}"
  for (name, content) in renderAll src sz tg ln bn heavyN do
    IO.FS.writeFile (path ++ "/" ++ name) (Gen.moduleHeader content)
  return 0
