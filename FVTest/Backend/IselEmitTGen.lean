import FV.Backend.Proof.IselEmitTFns

/-!
# Generator of the typed emission summary table (`FV/Backend/Proof/IselEmitTTab*.lean`)

Untrusted: `IselCovTGen` with the emission transfer functions (`aextET`, `actorET`, precondition
`apreET`, the typed oracle `aOracle`; `IselEmitTFns`): computes, by a fixpoint of the disjunctive
abstract interpreter (`aRule`, `AT`) over the exported ISLE rules, a summary table for every
internal term reachable from the rules of `lower` other than the hand-checked ones
(`emitHandIdsT`) on every instruction family (`famTab`), from the terminator rules of `lower` and
from the rules of `lower_branch` on every family (those ending in a branch, `aRuleLast`, without
their final `emit_side_effect`), and writes the table as Lean literals (`IselEmitTTabData`) with
leaf-wise `decide +kernel` checks split over modules (entry chunks `IselEmitTTabC*`, one theorem
per rule of `lower` in `IselEmitTTabS*`, `lower_branch` and the terminator rules in
`IselEmitTTabB`) and their assembly (`IselEmitTTab`). Rule constant names are read from
`FV/Backend/Proof/IselData.lean`. It also prints the failures (expected: none).

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselEmitTFns`):

    lake env lean --run FVTest/Backend/IselEmitTGen.lean FV/Backend/Proof
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.CovT
open Backend.Proof.Cov (NK internalOne)

deriving instance Hashable for Backend.OperandSize
deriving instance Hashable for Backend.Proof.CovT.AT

namespace Gen
open AT

def insAlt (b : AT) (as : List AT) (j : AT → AT → AT) : List AT :=
  match b with
  | .data t k fs =>
    if as.any (fun a => match a with | .data t' k' gs => t == t' && k == k' && fs.length == gs.length | _ => false)
    then as.map fun a => match a with
      | .data t' k' gs => if t == t' && k == k' && fs.length == gs.length then j a b else a
      | a => a
    else as ++ [b]
  | _ => as

partial def join : AT → AT → AT
  | .bot, b => b
  | a, .bot => a
  | .reg m, .reg n => .reg (m ||| n)
  | .ty a, .ty b => .ty (a ++ b.filter (!a.contains ·))
  | .num k b, .num k' b' => if k == k' then .num k (max b b') else .flat (if k == .callInfo || k' == .callInfo then 15 else 0) true
  | .val a, .val b => .val (a ++ b.filter (!a.contains ·))
  | .valsAll a, .valsAll b => .valsAll (a ++ b.filter (!a.contains ·))
  | .vals a, .vals b =>
    if a.length == b.length then .vals ((a.zip b).map fun (x, y) => x ++ y.filter (!x.contains ·))
    else .valsAll (a.flatten ++ b.flatten)
  | .vals a, .valsAll b => .valsAll (a.flatten ++ b)
  | .valsAll a, .vals b => .valsAll (a ++ b.flatten)
  | .inst a, .inst b => .inst (a ++ b.filter (!a.contains ·))
  | .data t k fs, .data t' k' gs =>
    if t == t' && k == k' && fs.length == gs.length then .data t k ((fs.zip gs).map fun (x, y) => join x y)
    else .alts [.data t k fs, .data t' k' gs]
  | .alts as, b@(.data ..) => .alts (insAlt b as join)
  | a@(.data ..), .alts bs => .alts (insAlt a bs join)
  | .alts as, .alts bs => .alts (bs.foldl (fun acc b => insAlt b acc join) as)
  | a, b => if a == b then a else
    let d := deep a; let e := deep b; .flat (d.1 ||| e.1) (d.2 && e.2)

abbrev Key := TermId × List AT

structure St where
  tab : Std.HashMap Key AT := {}
  old : Std.HashMap Key AT := {}
  changed : Bool := false
  bad : List (Nat × String) := []
  cur : Nat := 0
  from_ : Std.HashMap Key Nat := {}

def demand (t : TermId) (as : List AT) : StateM St AT := do
  let s ← get
  match s.tab.get? (t, as) with
  | some out => pure out
  | none =>
    let o := (s.old.get? (t, as)).getD .bot
    set { s with tab := s.tab.insert (t, as) o, changed := true, from_ := s.from_.insert (t, as) s.cur }
    pure o

variable (p : Program)

mutual
partial def iExpr : Isle.Expr → List AT → StateM St AT
  | .var _ x, env => pure (env.getD x .top)
  | .constBool _ b, _ => pure (.bool b)
  | .constInt _ n, _ => pure (aint n)
  | .constPrim tyv n, _ => pure (aprim tyv n)
  | .let _ bs body, env => do let env' ← iBinds bs env; iExpr body env'
  | .term tyv t args, env => do
    let as ← iArgs args env
    if as.any AT.isBot then pure .bot else
    match termOf p t with
    | .error _ => pure .top
    | .ok term =>
      match term.kind with
      | .enumVariant k => pure (.data tyv k as)
      | .struct => pure (.data tyv 0 as)
      | .decl _ (some (.external _)) _ =>
        if !apreET term.id as then
          modify fun s => { s with bad := (s.cur, s!"{term.name} {repr as}") :: s.bad }
        pure (actorET term.id as)
      | .decl _ (some .internal) _ =>
        match aOracle t as with
        | some a => pure a
        | none => demand t as
      | _ => pure .top
partial def iArgs : List Isle.Expr → List AT → StateM St (List AT)
  | [], _ => pure []
  | e :: es, env => do let a ← iExpr e env; let as ← iArgs es env; pure (a :: as)
partial def iBinds : List (VarId × TypeId × Isle.Expr) → List AT → StateM St (List AT)
  | [], env => pure env
  | (x, _, e) :: bs, env => do let a ← iExpr e env; iBinds bs (env.set x a)
end

partial def iIfLets : List IfLet → List AT → StateM St (List (List AT))
  | [], env => pure [env]
  | il :: ils, env => do
    let a ← iExpr p il.rhs env
    let mut out := []
    for e in aPat p aextET a il.lhs env do
      out := out ++ (← iIfLets ils e)
    pure out

def iRule (ins : List AT) (r : Rule) : StateM St AT := do
  modify fun s => { s with cur := r.id }
  let mut o := AT.bot
  for env0 in aPatArgs p aextET ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      o := join o (← iExpr p r.rhs env1)
  pure o

/-- The demands of `aLast`: everything but the final `emit_side_effect`. -/
partial def iLast : Nat → Isle.Expr → List AT → StateM St Unit
  | 0, _, _ => pure ()
  | n + 1, .term _ t args, env => do
    if t == TId.emit_side_effect then
      match args with
      | [e] => let _ ← iExpr p e env
      | _ => pure ()
    else
      let as ← iArgs p args env
      for r in p.rulesOf t do
        for env0 in aPatArgs p aextET as r.args (List.replicate r.vars.length .top) do
          for env1 in ← iIfLets p r.iflets env0 do
            iLast n r.rhs env1
  | n + 1, .let _ bs body, env => do
    let env' ← iBinds p bs env
    iLast n body env'
  | _ + 1, _, _ => pure ()

def lastFuel : Nat := 10

def iRuleLast (ins : List AT) (r : Rule) : StateM St Unit := do
  modify fun s => { s with cur := r.id }
  for env0 in aPatArgs p aextET ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      iLast p lastFuel r.rhs env1

/-- Roots: plain rules (`aRule`) and rules ending in a branch (`aRuleLast`). -/
structure Roots where
  plain : List (List AT × List Rule)
  last : List (List AT × List Rule)

def runRoots (roots : Roots) : StateM St Unit := do
  for (ins, rs) in roots.plain do
    for r in rs do
      let _ ← iRule p ins r
  for (ins, rs) in roots.last do
    for r in rs do
      iRuleLast p ins r

def round (roots : Roots) : StateM St Unit := do
  runRoots p roots
  let s ← get
  for ((t, ins), out) in s.tab.toList do
    let mut o := out
    for r in p.rulesOf t do
      o := join o (← iRule p ins r)
    let s ← get
    if o != out then set { s with tab := s.tab.insert (t, ins) o, changed := true }

def fix (roots : Roots) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let ((), s') := (round p roots).run { s with changed := false, bad := [] }
    if s'.changed then fix roots n s' else s'

def gcRound (roots : Roots) : StateM St Unit := do
  runRoots p roots
  let mut done : Std.HashSet Key := {}
  repeat
    let s ← get
    let todo := s.tab.toList.filter fun (x : Key × AT) => !done.contains x.1
    if todo.isEmpty then break
    for (k, _) in todo do
      done := done.insert k
      for r in p.rulesOf k.1 do
        let _ ← iRule p k.2 r

def fixGC (roots : Roots) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let s1 := fix p roots 100 s
    let ((), s2) := (gcRound p roots).run { tab := {}, old := s1.tab }
    let s3 := fix p roots 100 { tab := s2.tab }
    if s3.tab.size == s1.tab.size then s3 else fixGC roots n s3

/-- Syntactically, the expression ends in `emit_side_effect` (through `let`s and internal terms). -/
partial def endsLast : Nat → Isle.Expr → Bool
  | 0, _ => false
  | n + 1, .term _ t _ =>
    t == TId.emit_side_effect || (internalOne p t && (p.rulesOf t).all fun r => endsLast n r.rhs)
  | n + 1, .let _ _ body => endsLast n body
  | _, _ => false

end Gen

namespace Gen
open Backend.Proof.CovT

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

def entryLit (e : TermId × List AT × AT) : String :=
  s!"({e.1}, [{", ".intercalate (e.2.1.map awLit)}], {awLit e.2.2})"

def stmtRules : List Rule := (program.rulesOf TId.lower).filter fun r => !emitHandIdsT.contains r.id
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := program.rulesOf TId.lower_branch
def lastRules : List Rule := branchRules.filter fun r => endsLast program lastFuel r.rhs
def plainBranchRules : List Rule := branchRules.filter fun r => !endsLast program lastFuel r.rhs

def fams : List Nat := List.range famTab.length

def roots : Roots :=
  { plain := (fams.map fun i => ([.inst [i]], stmtRules)) ++ [([.c0], termRules)] ++
      (fams.map fun i => ([.inst [i], .c0], plainBranchRules))
    last := fams.map fun i => ([.inst [i], .c0], lastRules) }

def mkTab : Tab :=
  let s := fixGC program roots 10 {}
  (s.tab.toList.toArray.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && toString (repr a.1.2) < toString (repr b.1.2)))).toList.map
    fun ((t, ins), o) => (t, ins, o)

end Gen

namespace Gen
open Backend.Proof.CovT

/-- Entries per chunk of the table (one definition and one leaf-wise kernel proof per chunk). -/
def chunk : Nat := 88

def preamble (title doc imports : String) : String :=
  imports ++ "\n/-!\n# Emission conditions of the typed lowering: " ++ title ++ "\n\n" ++
  "GENERATED by `FVTest/Backend/IselEmitTGen.lean` (untrusted; regenerate with\n" ++
  "`lake env lean --run FVTest/Backend/IselEmitTGen.lean FV/Backend/Proof`). Do not edit by hand.\n\n" ++
  doc ++ "\n-/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 16000000\nset_option Elab.async false\n\n" ++
  "namespace Backend.Proof.CovT\n\nopen Backend Backend.Proof Isle Isle.Aarch64\n\n"

def okDefs : String := "/-- `chkTab`'s test of one entry. -/
abbrev emitEntryOkT (e : TermId × List AT × AT) : Bool :=
  (program.rulesOf e.1).all (aRule program emitTabT aextET actorET apreET aOracle e.2.1 e.2.2)

/-- The test of one rule of `lower`: a hand-checked one (`emitHandIdsT`), or it checks on every
family. -/
def emitStmtOkT (r : Rule) : Bool :=
  emitHandIdsT.contains r.id || (List.range famTab.length).all fun i =>
    aRule program emitTabT aextET actorET apreET aOracle [.inst [i]] AT.top r

/-- The test of one rule of `lower_branch`: on every family it checks without branches, or ends
in one (`aRuleLast`). -/
def emitBranchOkT (r : Rule) : Bool :=
  (List.range famTab.length).all fun i =>
    aRule program emitTabT aextET actorET apreET aOracle [.inst [i], .c0] AT.top r ||
    aRuleLast program emitTabT aextET actorET apreET aOracle 10 [.inst [i], .c0] r

"

/-- The rule constants of a term, in order, from `IselData.lean`'s `program_rulesOf_<t>`. -/
def ruleNames (src : String) (t : Nat) : List String :=
  match src.splitOn s!"theorem program_rulesOf_{t} : program.rulesOf {t} =" with
  | _ :: rest :: _ =>
    let line := ((rest.splitOn "\n").getD 1 "").trimAscii.toString
    -- a one-line list ends in `] := rfl` (e.g. term 687), a multi-line one in `]`
    let line := ((line.splitOn " := rfl").headD line).trimAscii.toString
    let line := String.ofList ((line.toList.drop 1).dropLast)
    (line.splitOn ", ").map (·.trimAscii.toString)
  | _ => []

def groups {α : Type} (n : Nat) (l : List α) : List (List α) :=
  (List.range ((l.length + n - 1) / n)).map fun k => (l.drop (k * n)).take n

def chunksPerMod : Nat := 2
def rulesPerMod : Nat := 10

/-- Rule/family pairs whose single kernel check exceeds the memory budget, with the environments
per chunk: rule 2267 on family 8 (256 environments, 32 per chunk), the vector-lane `select`/
`bitselect`-like rules 1222-1228 on family 2 (64 environments; 16 of them take 8 GB in one
`decide`, so 8 per chunk). -/
def heavy : List (String × Nat × Nat) :=
  [("rule_lower_2267", 8, 32), ("rule_lower_1222", 2, 8), ("rule_lower_1224", 2, 8),
   ("rule_lower_1226", 2, 8), ("rule_lower_1228", 2, 8)]

/-- The helpers of the chunked checks (emitted once per module that has a heavy rule). -/
def heavyDefs : String := "private theorem all_of_chunks {α : Type} (g : α → Bool) (L : List α) (k n : Nat)
    (hn : L.length ≤ n * k) (h : ∀ c < n, ((L.drop (c * k)).take k).all g = true) :
    L.all g = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.mul_zero] at hn; omega
    · exact h0
  have hc : j / k < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have hjk := Nat.div_add_mod' j k
  have hm := Nat.mod_lt j hk
  have hl : j % k < ((L.drop (j / k * k)).take k).length := by
    simp only [List.length_take, List.length_drop]; omega
  have := List.all_eq_true.1 (h _ hc) _ (List.getElem_mem hl)
  simp only [List.getElem_take, List.getElem_drop] at this
  simp only [hjk] at this
  exact this

/-- The rule test of one environment (`aRule`'s body). -/
private def envOkT (out : AT) (r : Rule) (env : List AT) : Bool :=
  match aExpr program emitTabT actorET apreET aOracle r.rhs env with
  | some a => AT.le a out
  | none => false

/-- `aRule` from chunk-wise checks of its environments. -/
private theorem aRule_of_chunks {ins : List AT} {out : AT} {r : Rule} (k n : Nat)
    (hs : (aRuleEnvs program emitTabT aextET actorET apreET aOracle ins r).isSome = true)
    (hn : ((aRuleEnvs program emitTabT aextET actorET apreET aOracle ins r).getD []).length ≤ n * k)
    (h : ∀ c < n, ((((aRuleEnvs program emitTabT aextET actorET apreET aOracle ins r).getD []).drop
      (c * k)).take k).all (envOkT out r) = true) :
    aRule program emitTabT aextET actorET apreET aOracle ins out r = true := by
  unfold aRule
  cases he : aRuleEnvs program emitTabT aextET actorET apreET aOracle ins r with
  | none => rw [he] at hs; cases hs
  | some envs =>
    rw [he] at hn h
    exact all_of_chunks _ envs k n hn h

"

/-- The chunked check of heavy rule `r` on family `i` with `nc` environment chunks of `k`. -/
def heavyThm (r : String) (i k nc : Nat) : String := Id.run do
  let envs := s!"(aRuleEnvs program emitTabT aextET actorET apreET aOracle [.inst [{i}]] {r})"
  let mut s := s!"theorem emitStmtOkT_{r}_f{i}_s : {envs}.isSome = true := by decide +kernel\n\n"
  s := s ++ s!"theorem emitStmtOkT_{r}_f{i}_n : ({envs}.getD []).length ≤ {nc} * {k} := by decide +kernel\n\n"
  for c in List.range nc do
    s := s ++ s!"theorem emitStmtOkT_{r}_f{i}_c{c} : ((({envs}.getD []).drop ({c} * {k})).take {k}).all\n    (envOkT (AT.top) {r}) = true := by decide +kernel\n\n"
  s := s ++ s!"theorem emitStmtOkT_{r}_rest : (List.range famTab.length).all (fun i => i == {i} ||\n    aRule program emitTabT aextET actorET apreET aOracle [.inst [i]] AT.top {r}) = true := by\n  decide +kernel\n\n"
  s := s ++ s!"theorem emitStmtOkT_{r} : emitStmtOkT {r} = true := by\n  unfold emitStmtOkT\n  rw [Bool.or_eq_true]\n  refine .inr ?_\n  rw [List.all_eq_true]\n  intro i hi\n  by_cases hi' : i = {i}\n  · subst hi'\n    refine aRule_of_chunks {k} {nc} emitStmtOkT_{r}_f{i}_s emitStmtOkT_{r}_f{i}_n ?_\n    intro c hc\n    match c, hc with\n"
  for c in List.range nc do
    s := s ++ s!"    | {c}, _ => exact emitStmtOkT_{r}_f{i}_c{c}\n"
  s := s ++ s!"    | _ + {nc}, hc => exact absurd hc (by omega)\n  · have := List.all_eq_true.1 emitStmtOkT_{r}_rest i hi\n    simpa [hi'] using this\n\n"
  s

def renderAll (tab : Tab) (lowerNames branchNames : List String)
    (heavyN : List (String × Nat × Nat × Nat)) :
    List (String × String) := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut files : List (String × String) := []
  -- the table
  let mut d := preamble "the summary table"
    "`emitTabT`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of the rules of `lower` other than the hand-checked ones (`emitHandIdsT`) and of
`lower_branch` on every instruction family (`famTab`), and of the terminator rules of `lower`.
The leaf-wise kernel checks are in `IselEmitTTabC*` (entries), `IselEmitTTabS*` (the rules of
`lower`), `IselEmitTTabB` (`lower_branch`, terminators); `IselEmitTTab` assembles them."
    "import FV.Backend.Proof.IselEmitTFns\n"
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    d := d ++ s!"/-- Chunk {k} of the table. -/\ndef emitTabT{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  d := d ++ "/-- **The summary table.** -/\ndef emitTabT : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"emitTabT{·}")) ++ "\n\n"
  d := d ++ okDefs ++ "end Backend.Proof.CovT\n"
  files := files ++ [("IselEmitTTabData.lean", d)]
  -- entry chunks
  let cgs := groups chunksPerMod (List.range n)
  for (ks, gi) in cgs.zipIdx do
    let mut c := preamble s!"table entries, group {gi}" "Every rule of every entry of these chunks checks." "import FV.Backend.Proof.IselEmitTTabData\n"
    for k in ks do
      c := c ++ s!"theorem emitTabT{k}_ok : (emitTabT{k}).all emitEntryOkT = true := by\n  simp only [emitTabT{k}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
    files := files ++ [(s!"IselEmitTTabC{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  -- statement rules
  let sgs := groups rulesPerMod lowerNames
  for (rs, gi) in sgs.zipIdx do
    let mut c := preamble s!"rules of `lower`, group {gi}" "Each rule of `lower` is hand-checked or checks on every family (`emitStmtOkT`)." "import FV.Backend.Proof.IselEmitTTabData\n"
    if rs.any (fun r => heavyN.any (·.1 == r)) then c := c ++ heavyDefs
    for r in rs do
      match heavyN.find? (·.1 == r) with
      | some (_, i, k, nc) => c := c ++ heavyThm r i k nc
      | none => c := c ++ s!"theorem emitStmtOkT_{r} : emitStmtOkT {r} = true := by decide +kernel\n\n"
    files := files ++ [(s!"IselEmitTTabS{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  -- branch rules and terminators
  let mut bc := preamble "rules of `lower_branch`, terminators" "Each rule of `lower_branch` checks on every family (`emitBranchOkT`); the terminator rules of `lower` (964 `return`, 1037 `trap`) check on `c0`." "import FV.Backend.Proof.IselEmitTTabData\n"
  for r in branchNames do
    bc := bc ++ s!"theorem emitBranchOkT_{r} : emitBranchOkT {r} = true := by decide +kernel\n\n"
  bc := bc ++ "/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem emitTermT_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program emitTabT aextET actorET apreET aOracle [.c0] AT.top r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

"
  files := files ++ [("IselEmitTTabB.lean", bc ++ "end Backend.Proof.CovT\n")]
  -- assembly
  let imps := "import FV.Backend.Proof.IselEmitTTabB\n" ++
    String.join ((List.range cgs.length).map (s!"import FV.Backend.Proof.IselEmitTTabC{·}\n")) ++
    String.join ((List.range sgs.length).map (s!"import FV.Backend.Proof.IselEmitTTabS{·}\n"))
  let mut m := preamble "the table and root checks"
    "`emitTabT_ok`: every rule of every entry checks (`chkTab`); `emitStmtT_ok`: every rule of
`lower` other than the hand-checked ones (`emitHandIdsT`) checks on every family; `emitTermT_ok`
(`IselEmitTTabB`): the terminator rules of `lower` check; `emitBranchT_ok`: every rule of
`lower_branch` checks on every family, without branches or ending in one."
    imps
  m := m ++ "/-- **Every rule of every entry checks.** -/\ntheorem emitTabT_ok : chkTab program emitTabT aextET actorET apreET aOracle = true := by\n  unfold chkTab\n  show (emitTabT).all emitEntryOkT = true\n  simp only [emitTabT, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"emitTabT{·}_ok")) ++ ", Bool.and_self]\n\n"
  m := m ++ "/-- **Every rule of `lower` is hand-checked or checks on every family** (`emitStmtOkT`). -/\ntheorem emitStmtT_ok : (program.rulesOf TId.lower).all emitStmtOkT = true := by\n  rw [show TId.lower = 686 from rfl, program_rulesOf_686]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
    ", ".intercalate (lowerNames.map (s!"emitStmtOkT_{·}")) ++ "]\n\n"
  m := m ++ "/-- **Every rule of `lower_branch` checks on every family** (`emitBranchOkT`). -/\ntheorem emitBranchT_ok : (program.rulesOf TId.lower_branch).all emitBranchOkT = true := by\n  rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
    ", ".intercalate (branchNames.map (s!"emitBranchOkT_{·}")) ++ "]\n\n"
  files := files ++ [("IselEmitTTab.lean", m ++ "end Backend.Proof.CovT\n")]
  files

end Gen

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselEmitTGen <out dir>"; return 1
  let s := fixGC program roots 10 {}
  let tab := mkTab
  let ok := chkTab program tab aextET actorET apreET aOracle
  IO.println s!"entries {tab.length} chkTab {ok}"
  for (rid, msg) in s.bad.eraseDups do IO.println s!"bad emit in rule {rid}: {msg.take 600}"
  let tmap : Std.HashMap Gen.Key AT := tab.foldl (fun m e => m.insert (e.1, e.2.1) e.2.2) {}
  let ((), sd) := (Gen.gcRound program roots).run { old := tmap }
  let froms := sd.from_
  for e in tab do
    for r in program.rulesOf e.1 do
      if !aRule program tab aextET actorET apreET aOracle e.2.1 e.2.2 r then
        IO.println s!"  tab fail term {e.1} rule {r.id} ins {(e.2.1.map awLit)} out {awLit e.2.2} from rule {froms.get? (e.1, e.2.1)}"
        match aRuleEnvs program tab aextET actorET apreET aOracle e.2.1 r with
        | none => IO.println "    envs: none (an if-let/arg check failed)"
        | some envs =>
          for env in envs do
            match aExpr program tab actorET apreET aOracle r.rhs env with
            | none => IO.println s!"    rhs none; env {(env.map awLit)}"
            | some a => IO.println s!"    rhs {awLit a}"
  let mut allOk := ok
  for i in fams do
    let topBad := stmtRules.filter fun r => !aRule program tab aextET actorET apreET aOracle [.inst [i]] AT.top r
    if !topBad.isEmpty then
      allOk := false
      IO.println s!"family {i}: top-fail {topBad.map (·.id)}"
    for r in stmtRules do
      let ne := ((aRuleEnvs program tab aextET actorET apreET aOracle [.inst [i]] r).getD []).length
      if ne > 48 then IO.println s!"  many envs: family {i} rule {r.id}: {ne}"
  let termBad := termRules.filter fun r => !aRule program tab aextET actorET apreET aOracle [.c0] AT.top r
  IO.println s!"term [.c0] fails {termBad.map (·.id)}"
  let term := termBad.isEmpty
  let mut br := true
  for i in fams do
    let bad := branchRules.filter fun r =>
      !(aRule program tab aextET actorET apreET aOracle [.inst [i], .c0] AT.top r ||
        aRuleLast program tab aextET actorET apreET aOracle lastFuel [.inst [i], .c0] r)
    if !bad.isEmpty then
      br := false
      IO.println s!"branch family {i} fails {bad.map (·.id)}"
  IO.println s!"term {term} branch {br} last {lastRules.map (·.id)}"
  let src ← IO.FS.readFile "FV/Backend/Proof/IselData.lean"
  let ln := ruleNames src 686
  let bn := ruleNames src 687
  IO.println s!"lower rules {ln.length} branch rules {bn.length}"
  if ln.length != (program.rulesOf TId.lower).length || bn.length != branchRules.length then
    IO.eprintln "rule name lists do not match the program"; return 1
  let heavyN := heavy.filterMap fun (name, i, k) => ((ln.zip (program.rulesOf TId.lower)).find? (·.1 == name)).map
    fun (_, r) =>
      let ne := ((aRuleEnvs program tab aextET actorET apreET aOracle [.inst [i]] r).getD []).length
      (name, i, k, (ne + k - 1) / k)
  IO.println s!"heavy {heavyN}"
  for (name, content) in renderAll tab ln bn heavyN do
    IO.FS.writeFile (path ++ "/" ++ name) content
  return (if allOk && term && br then 0 else 1)
