import FV.Backend.Proof.IselCovTFns

/-!
# Generator of the typed V3 coverage summary table (`FV/Backend/Proof/IselCovTTab*.lean`)

Untrusted: computes, by a fixpoint of the disjunctive abstract interpreter (`aRule`, `AT`) over
the exported ISLE rules, a summary table for every internal term reachable from every rule of
`lower` and `lower_branch` on every instruction family (`famTab`), and writes the table as Lean
literals (`IselCovTTabData`) with leaf-wise `decide +kernel` checks split over modules (entry
chunks `IselCovTTabC*`, one theorem per rule of `lower` in `IselCovTTabS*`, `lower_branch` and the
terminator rules in `IselCovTTabB`) and their assembly (`IselCovTTab`). Rule constant names are
read from `FV/Backend/Proof/IselData.lean`. It also prints the per-family failures (expected: none).

Regenerate (from the repository root, after `lake build FV.Backend.Proof.IselCovTFns`):

    lake env lean --run FVTest/Backend/IselCovTGen.lean FV/Backend/Proof
-/

open Isle Isle.Aarch64 Isle.Interp Backend Backend.Proof Backend.Proof.CovT
open Backend.Proof.Cov (NK)

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
        if !apre term.id as then
          modify fun s => { s with bad := (s.cur, s!"{term.name} {repr as}") :: s.bad }
        pure (actor term.id as)
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
    for e in aPat p aext a il.lhs env do
      out := out ++ (← iIfLets ils e)
    pure out

def iRule (ins : List AT) (r : Rule) : StateM St AT := do
  modify fun s => { s with cur := r.id }
  let mut o := AT.bot
  for env0 in aPatArgs p aext ins r.args (List.replicate r.vars.length .top) do
    for env1 in ← iIfLets p r.iflets env0 do
      o := join o (← iExpr p r.rhs env1)
  pure o

def round (roots : List (List AT × List Rule)) : StateM St Unit := do
  for (ins, rs) in roots do
    for r in rs do
      let _ ← iRule p ins r
  let s ← get
  for ((t, ins), out) in s.tab.toList do
    let mut o := out
    for r in p.rulesOf t do
      o := join o (← iRule p ins r)
    let s ← get
    if o != out then set { s with tab := s.tab.insert (t, ins) o, changed := true }

def fix (roots : List (List AT × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let ((), s') := (round p roots).run { s with changed := false, bad := [] }
    if s'.changed then fix roots n s' else s'

def gcRound (roots : List (List AT × List Rule)) : StateM St Unit := do
  for (ins, rs) in roots do
    for r in rs do
      let _ ← iRule p ins r
  let mut done : Std.HashSet Key := {}
  repeat
    let s ← get
    let todo := s.tab.toList.filter fun (x : Key × AT) => !done.contains x.1
    if todo.isEmpty then break
    for (k, _) in todo do
      done := done.insert k
      for r in p.rulesOf k.1 do
        let _ ← iRule p k.2 r

def fixGC (roots : List (List AT × List Rule)) : Nat → St → St
  | 0, s => s
  | n + 1, s =>
    let s1 := fix p roots 100 s
    let ((), s2) := (gcRound p roots).run { tab := {}, old := s1.tab }
    let s3 := fix p roots 100 { tab := s2.tab }
    if s3.tab.size == s1.tab.size then s3 else fixGC roots n s3

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

def stmtRules : List Rule := program.rulesOf TId.lower
def termRules : List Rule := (program.rulesOf TId.lower).filter fun r => r.id == 964 || r.id == 1037
def branchRules : List Rule := program.rulesOf TId.lower_branch

def roots : List (List AT × List Rule) :=
  ((List.range famTab.length).map fun i => ([.inst [i]], stmtRules)) ++
    ((List.range famTab.length).map fun i => ([.inst [i], .c0], branchRules))

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
  imports ++ "\n/-!\n# Form coverage over float-capable contexts (typed V3): " ++ title ++ "\n\n" ++
  "GENERATED by `FVTest/Backend/IselCovTGen.lean` (untrusted; regenerate with\n" ++
  "`lake env lean --run FVTest/Backend/IselCovTGen.lean FV/Backend/Proof`). Do not edit by hand.\n\n" ++
  doc ++ "\n-/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 16000000\nset_option Elab.async false\n\n" ++
  "namespace Backend.Proof.CovT\n\nopen Backend Backend.Proof Isle Isle.Aarch64\n\n"

def dataDefs : String := "/-- The result of a statement of family `i`: registers of the family's result classes. -/
def famOut (i : Nat) : AT :=
  let F := famTab.getD i default
  if F.all.isEmpty then AT.top else .flat (vcls F.all) true

/-- The output a rule of `lower` is checked against on family `i`: the family's result classes,
any result for the `call` rules 1031-1033 (their results by hand, `Cov.out_callT`). -/
def stmtOut (r : Rule) (i : Nat) : AT :=
  if r.id == 1031 || r.id == 1032 || r.id == 1033 then AT.top else famOut i

"

def okDefs : String := "/-- `chkTab`'s test of one entry. -/
abbrev covEntryOkT (e : TermId × List AT × AT) : Bool :=
  (program.rulesOf e.1).all (aRule program covTabT aext actor apre aOracle e.2.1 e.2.2)

/-- The test of one rule of `lower`: it checks on every family, with output `stmtOut`. -/
def stmtOkT (r : Rule) : Bool :=
  (List.range famTab.length).all fun i =>
    aRule program covTabT aext actor apre aOracle [.inst [i]] (stmtOut r i) r

/-- The test of one rule of `lower_branch`: it checks on every family. -/
def branchOkT (r : Rule) : Bool :=
  (List.range famTab.length).all fun i =>
    aRule program covTabT aext actor apre aOracle [.inst [i], .c0] AT.top r

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

/-- Rule/family pairs whose single kernel check exceeds the memory budget (rule 2267 on family
8 has 256 environments, >22G in one `decide`): checked in `envChunk`-sized environment chunks. -/
def heavy : List (String × Nat) := [("rule_lower_2267", 8)]
def envChunk : Nat := 32

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
  match aExpr program covTabT actor apre aOracle r.rhs env with
  | some a => AT.le a out
  | none => false

/-- `aRule` from chunk-wise checks of its environments. -/
private theorem aRule_of_chunks {ins : List AT} {out : AT} {r : Rule} (k n : Nat)
    (hs : (aRuleEnvs program covTabT aext actor apre aOracle ins r).isSome = true)
    (hn : ((aRuleEnvs program covTabT aext actor apre aOracle ins r).getD []).length ≤ n * k)
    (h : ∀ c < n, ((((aRuleEnvs program covTabT aext actor apre aOracle ins r).getD []).drop
      (c * k)).take k).all (envOkT out r) = true) :
    aRule program covTabT aext actor apre aOracle ins out r = true := by
  unfold aRule
  cases he : aRuleEnvs program covTabT aext actor apre aOracle ins r with
  | none => rw [he] at hs; cases hs
  | some envs =>
    rw [he] at hn h
    exact all_of_chunks _ envs k n hn h

"

/-- The chunked check of heavy rule `r` on family `i` with `nc` environment chunks. -/
def heavyThm (r : String) (i nc : Nat) : String := Id.run do
  let envs := s!"(aRuleEnvs program covTabT aext actor apre aOracle [.inst [{i}]] {r})"
  let k := envChunk
  let mut s := s!"theorem stmtOkT_{r}_f{i}_s : {envs}.isSome = true := by decide +kernel\n\n"
  s := s ++ s!"theorem stmtOkT_{r}_f{i}_n : ({envs}.getD []).length ≤ {nc} * {k} := by decide +kernel\n\n"
  for c in List.range nc do
    s := s ++ s!"theorem stmtOkT_{r}_f{i}_c{c} : ((({envs}.getD []).drop ({c} * {k})).take {k}).all\n    (envOkT (stmtOut {r} {i}) {r}) = true := by decide +kernel\n\n"
  s := s ++ s!"theorem stmtOkT_{r}_rest : (List.range famTab.length).all (fun i => i == {i} ||\n    aRule program covTabT aext actor apre aOracle [.inst [i]] (stmtOut {r} i) {r}) = true := by\n  decide +kernel\n\n"
  s := s ++ s!"theorem stmtOkT_{r} : stmtOkT {r} = true := by\n  unfold stmtOkT\n  rw [List.all_eq_true]\n  intro i hi\n  by_cases hi' : i = {i}\n  · subst hi'\n    refine aRule_of_chunks {k} {nc} stmtOkT_{r}_f{i}_s stmtOkT_{r}_f{i}_n ?_\n    intro c hc\n    match c, hc with\n"
  for c in List.range nc do
    s := s ++ s!"    | {c}, _ => exact stmtOkT_{r}_f{i}_c{c}\n"
  s := s ++ s!"    | _ + {nc}, hc => exact absurd hc (by omega)\n  · have := List.all_eq_true.1 stmtOkT_{r}_rest i hi\n    simpa [hi'] using this\n\n"
  s

def renderAll (tab : Tab) (lowerNames branchNames : List String) (heavyN : List (String × Nat × Nat)) :
    List (String × String) := Id.run do
  let n := (tab.length + chunk - 1) / chunk
  let mut files : List (String × String) := []
  -- the table
  let mut d := preamble "the summary table"
    "`covTabT`: per entry an internal term, abstract inputs and an abstract output, closed under the
calls of every rule of `lower` and `lower_branch` on every instruction family (`famTab`).
The leaf-wise kernel checks are in `IselCovTTabC*` (entries), `IselCovTTabS*` (the rules of
`lower`), `IselCovTTabB` (`lower_branch`, terminators); `IselCovTTab` assembles them."
    "import FV.Backend.Proof.IselCovTFns\n"
  d := d ++ dataDefs
  for k in [0:n] do
    let es := (tab.drop (k * chunk)).take chunk
    d := d ++ s!"/-- Chunk {k} of the table. -/\ndef covTabT{k} : Tab := [\n  " ++
      ",\n  ".intercalate (es.map entryLit) ++ "]\n\n"
  d := d ++ "/-- **The summary table.** -/\ndef covTabT : Tab :=\n  " ++
    " ++ ".intercalate ((List.range n).map (s!"covTabT{·}")) ++ "\n\n"
  d := d ++ okDefs ++ "end Backend.Proof.CovT\n"
  files := files ++ [("IselCovTTabData.lean", d)]
  -- entry chunks
  let cgs := groups chunksPerMod (List.range n)
  for (ks, gi) in cgs.zipIdx do
    let mut c := preamble s!"table entries, group {gi}" "Every rule of every entry of these chunks checks." "import FV.Backend.Proof.IselCovTTabData\n"
    for k in ks do
      c := c ++ s!"theorem covTabT{k}_ok : (covTabT{k}).all covEntryOkT = true := by\n  simp only [covTabT{k}, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
    files := files ++ [(s!"IselCovTTabC{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  -- statement rules
  let sgs := groups rulesPerMod lowerNames
  for (rs, gi) in sgs.zipIdx do
    let mut c := preamble s!"rules of `lower`, group {gi}" "Each rule of `lower` checks on every family (`stmtOkT`)." "import FV.Backend.Proof.IselCovTTabData\n"
    if rs.any (fun r => heavyN.any (·.1 == r)) then c := c ++ heavyDefs
    for r in rs do
      match heavyN.find? (·.1 == r) with
      | some (_, i, nc) => c := c ++ heavyThm r i nc
      | none => c := c ++ s!"theorem stmtOkT_{r} : stmtOkT {r} = true := by decide +kernel\n\n"
    files := files ++ [(s!"IselCovTTabS{gi}.lean", c ++ "end Backend.Proof.CovT\n")]
  -- branch rules and terminators
  let mut bc := preamble "rules of `lower_branch`, terminators" "Each rule of `lower_branch` checks on every family (`branchOkT`); the terminator rules of `lower` (964 `return`, 1037 `trap`) check on `c0`." "import FV.Backend.Proof.IselCovTTabData\n"
  for r in branchNames do
    bc := bc ++ s!"theorem branchOkT_{r} : branchOkT {r} = true := by decide +kernel\n\n"
  bc := bc ++ "/-- The terminator rules of `lower` (964 `return`, 1037 `trap`) check. -/
theorem covTermT_ok : (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
    aRule program covTabT aext actor apre aOracle [.c0] AT.top r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

"
  files := files ++ [("IselCovTTabB.lean", bc ++ "end Backend.Proof.CovT\n")]
  -- assembly
  let imps := "import FV.Backend.Proof.IselCovTTabB\n" ++
    String.join ((List.range cgs.length).map (s!"import FV.Backend.Proof.IselCovTTabC{·}\n")) ++
    String.join ((List.range sgs.length).map (s!"import FV.Backend.Proof.IselCovTTabS{·}\n"))
  let mut m := preamble "the table and root checks"
    "`covTabT_ok`: every rule of every entry checks (`chkTab`); `covStmtT_ok`: every rule of `lower`
checks on every family, with the family's result classes (`famOut`) except the `call` rules
1031-1033 (any result; their results by hand); `covTermT_ok` (`IselCovTTabB`): the terminator
rules of `lower` check; `covBranchT_ok`: every rule of `lower_branch` checks on every family."
    imps
  m := m ++ "/-- **Every rule of every entry checks.** -/\ntheorem covTabT_ok : chkTab program covTabT aext actor apre aOracle = true := by\n  unfold chkTab\n  show (covTabT).all covEntryOkT = true\n  simp only [covTabT, List.all_append, " ++
    ", ".intercalate ((List.range n).map (s!"covTabT{·}_ok")) ++ ", Bool.and_self]\n\n"
  m := m ++ "/-- **Every rule of `lower` checks on every family** (`stmtOkT`). -/\ntheorem covStmtT_ok : (program.rulesOf TId.lower).all stmtOkT = true := by\n  rw [show TId.lower = 686 from rfl, program_rulesOf_686]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
    ", ".intercalate (lowerNames.map (s!"stmtOkT_{·}")) ++ "]\n\n"
  m := m ++ "/-- **Every rule of `lower_branch` checks on every family** (`branchOkT`). -/\ntheorem covBranchT_ok : (program.rulesOf TId.lower_branch).all branchOkT = true := by\n  rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]\n  simp only [List.all_cons, List.all_nil, Bool.and_true, " ++
    ", ".intercalate (branchNames.map (s!"branchOkT_{·}")) ++ "]\n\n"
  files := files ++ [("IselCovTTab.lean", m ++ "end Backend.Proof.CovT\n")]
  files

end Gen

open Gen in
def famOut (i : Nat) : AT :=
  let F := famTab.getD i default
  if F.all.isEmpty then AT.top else .flat (vcls F.all) true

open Gen in
def stmtOut (r : Rule) (i : Nat) : AT :=
  if r.id == 1031 || r.id == 1032 || r.id == 1033 then AT.top else famOut i

open Gen in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: IselCovTGen <out dir>"; return 1
  let tab := mkTab
  let ok := chkTab program tab aext actor apre aOracle
  IO.println s!"entries {tab.length} chkTab {ok}"
  let tmap : Std.HashMap Gen.Key AT := tab.foldl (fun m e => m.insert (e.1, e.2.1) e.2.2) {}
  let ((), sd) := (Gen.gcRound program roots).run { old := tmap }
  let froms := sd.from_
  for e in tab do
    for r in program.rulesOf e.1 do
      if !aRule program tab aext actor apre aOracle e.2.1 e.2.2 r then
        IO.println s!"  tab fail term {e.1} rule {r.id} ins {(e.2.1.map awLit)} out {awLit e.2.2} from rule {froms.get? (e.1, e.2.1)}"
        match aRuleEnvs program tab aext actor apre aOracle e.2.1 r with
        | none => IO.println "    envs: none (an if-let/arg check failed)"
        | some envs =>
          for env in envs do
            match aExpr program tab actor apre aOracle r.rhs env with
            | none => IO.println s!"    rhs none; env {(env.map awLit)}"
            | some a => IO.println s!"    rhs {awLit a}"
  let mut allOk := ok
  for i in List.range famTab.length do
    let topBad := stmtRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i]] AT.top r
    let resBad := stmtRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i]] (stmtOut r i) r
    if !topBad.isEmpty || !resBad.isEmpty then allOk := false
    IO.println s!"family {i}: top-fail {topBad.map (·.id)} res-fail {resBad.map (·.id)}"
  let termBad := termRules.filter fun r => !aRule program tab aext actor apre aOracle [.c0] AT.top r
  IO.println s!"term [.c0] fails {termBad.map (·.id)}"
  let term := termBad.isEmpty
  let mut br := true
  for i in List.range famTab.length do
    let bad := branchRules.filter fun r => !aRule program tab aext actor apre aOracle [.inst [i], .c0] AT.top r
    if !bad.isEmpty then
      br := false
      IO.println s!"branch family {i} fails {bad.map (·.id)}"
  IO.println s!"term {term} branch {br}"
  let src ← IO.FS.readFile "FV/Backend/Proof/IselData.lean"
  let ln := ruleNames src 686
  let bn := ruleNames src 687
  IO.println s!"lower rules {ln.length} branch rules {bn.length}"
  if ln.length != stmtRules.length || bn.length != branchRules.length then
    IO.eprintln "rule name lists do not match the program"; return 1
  let heavyN := heavy.filterMap fun (name, i) => ((ln.zip stmtRules).find? (·.1 == name)).map
    fun (_, r) =>
      let ne := ((aRuleEnvs program tab aext actor apre aOracle [.inst [i]] r).getD []).length
      (name, i, (ne + envChunk - 1) / envChunk)
  IO.println s!"heavy {heavyN}"
  for (name, content) in renderAll tab ln bn heavyN do
    IO.FS.writeFile (path ++ "/" ++ name) content
  return (if allOk && term && br then 0 else 1)
