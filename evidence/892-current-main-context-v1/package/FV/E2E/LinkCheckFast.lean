import FV.E2E.LinkScopeFast

/-! # The checker's program-level checks with hash maps (T3d)

`linkChks` and `globalChks` (`FV/E2E/LinkCheck.lean`, the checks of `okB`) look a name up in the
program (`Clif.Program.func?`), in the CLIF image's symbols and in the link map (`List.lookup`)
at every call site, declaration and symbol, scan every function's externs for every function
(`calleeB`), evaluate `g`'s own facts (`indFreeB g`, `declB g`, `indSigs g`) for every pair
(`g`, `h`) of functions, every link-map entry for every function (`symInjB`), and every function
of the table for every call (`raCallB`, recomputing the call's offset `lineOffset` for each):
hours of `link-check` on a 28k-function program (std through `cargo fv --build-std`).

`LinkCtx.of I P T` computes the lookups once (hash maps: `assocMap`, `funcMap`, `addrGroups`,
`calleeSet`; the table's code ranges `RaEnt`); `linkChksWith (LinkCtx.of I P T) P g r =
linkChks I P T g r` (`linkChksWith_of`) and `globalChksWith (LinkCtx.of I P T) I P T =
globalChks I P T` (`globalChksWith_of`). `link-check` evaluates these. No statement changes.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

/-! ## `raCallB` -/

/-- A function of the table with its code range: `lo` its base, `hi` the end of its words, `fits`
that they fit the address space (`outside`'s first conjunct). -/
structure RaEnt where
  name : String
  fits : Bool
  lo : Nat
  hi : Nat
  art : Art

def RaEnt.of (e : Clif.Function × Art) : RaEnt :=
  let lo := e.2.base.toNat
  let hi := lo + 4 * e.2.fb.words.size
  ⟨e.1.name, decide (hi ≤ 2 ^ 64), lo, hi, e.2⟩

/-- `raCallB`'s test of one function of the table at a call of `g` (named `gn`) at `pc`, with
`r = (pc + 4).toNat`: the range test first (`outside`), then the names, then `raOkB`. -/
def RaEnt.okAt (x : RaEnt) (gn : String) (pc : BitVec 64) (r : Nat) : Bool :=
  (x.fits && (decide (r < x.lo) || decide (x.hi ≤ r))) || x.name == gn || raOkB x.art pc

theorem RaEnt.okAt_of (e : Clif.Function × Art) (gn : String) (pc : BitVec 64) :
    (RaEnt.of e).okAt gn pc (pc + 4).toNat = (e.1.name == gn || raOkB e.2 pc) := by
  show (outside (pc + 4) e.2 || e.1.name == gn || raOkB e.2 pc) = _
  cases hx : outside (pc + 4) e.2
  · simp
  · have : raOkB e.2 pc = true := by unfold raOkB; rw [hx]; rfl
    simp [this]

/-- The offsets of the lines `ls` from `acc` on: `acc + lineOffset ls j` at `j`
(`offsList_get`). -/
def offsList : List Line → Nat → List Nat
  | [], acc => [acc]
  | l :: ls, acc => acc :: offsList ls (acc + l.size)

theorem offsList_get : ∀ (ls : List Line) (acc j : Nat), j ≤ ls.length →
    (offsList ls acc)[j]? = some (acc + lineOffset ls j)
  | [], acc, j, h => by
    have : j = 0 := by simpa using h
    subst this; simp [offsList, lineOffset]
  | l :: ls, acc, 0, _ => by simp [offsList, lineOffset]
  | l :: ls, acc, j + 1, h => by
    simp only [offsList, List.getElem?_cons_succ]
    rw [offsList_get ls (acc + l.size) j (by simpa using h)]
    simp [lineOffset, List.take_succ_cons, Nat.add_assoc]

/-- **`raCallB` with the table's code ranges precomputed** (`E`, `raCallFastB_eq`) and the call
offsets computed once per function. -/
def raCallFastB (E : List RaEnt) (g : Clif.Function) (a : Art) : Bool :=
  let offs := (offsList a.fa.lines.toList 0).toArray
  let gn := g.name
  (List.range a.fa.lines.size).all fun j =>
    match a.fa.lines[j]? with
    | some l => !callLine l ||
        let pc := a.base + BitVec.ofNat 64 (offs[j]?.getD 0)
        let r := (pc + 4).toNat
        E.all fun x => x.okAt gn pc r
    | none => true

theorem all_range_congr {n : Nat} {f f' : Nat → Bool} (h : ∀ j < n, f j = f' j) :
    (List.range n).all f = (List.range n).all f' := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun hf j hj => h j hj ▸ hf j hj, fun hf j hj => (h j hj).symm ▸ hf j hj⟩

theorem raCallFastB_eq (T : List (Clif.Function × Art)) (g : Clif.Function) (a : Art) :
    raCallFastB (T.map RaEnt.of) g a = raCallB T g a := by
  unfold raCallFastB raCallB
  refine all_range_congr fun j hj => ?_
  cases a.fa.lines[j]? with
  | none => rfl
  | some l =>
    have ho : (offsList a.fa.lines.toList 0).toArray[j]?.getD 0 = lineOffset a.fa.lines.toList j := by
      rw [List.getElem?_toArray, offsList_get _ _ _ (by simp; omega)]
      simp
    simp only [ho, List.all_map, Function.comp_def, RaEnt.okAt_of]

/-! ## `g`'s call sites -/

/-- `siteOk` with the program's functions looked up through `F` (`siteOk P = siteWithOk P.func? P`,
by definition). -/
def siteWithOk (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (vc : VCode) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => true
  | .reg _ => blrOk P may (gotOf vc) info

theorem siteWithOk_func? (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool)
    (vc : VCode) : siteWithOk P.func? P g may vc = siteOk P g may vc := rfl

/-! ## The program's callees and link map -/

/-- The names `g` declares, added to `s`. -/
def calleeStep (s : Std.HashSet String) (g : Clif.Function) : Std.HashSet String :=
  g.externs.foldl (fun s e => s.insert e.2.name) s

theorem calleeGo_contains (n : String) :
    ∀ (fs : List Clif.Function) (s : Std.HashSet String),
      (fs.foldl calleeStep s).contains n = (s.contains n || fs.any fun g => g.externs.any (·.2.name == n))
  | [], s => by simp
  | g :: fs, s => by
    rw [List.foldl_cons, calleeGo_contains n fs, calleeStep, foldl_insert_name_contains, List.any_cons,
      Bool.or_assoc]

/-- The names the program's functions declare (`calleeB`'s first disjunct: `calleeSet_contains`). -/
def calleeSet (P : Clif.Program) : Std.HashSet String := P.funcs.foldl calleeStep {}

theorem calleeSet_contains (P : Clif.Program) (n : String) :
    (calleeSet P).contains n = P.funcs.any fun g => g.externs.any (·.2.name == n) := by
  simp [calleeSet, calleeGo_contains]

/-- The names of the link-map entries by address modulo `2 ^ 64` (`symInjB`'s inner scan:
`addrGroups_getD`). -/
def addrGroups (l : List (String × Nat)) : Std.HashMap Nat (List String) :=
  l.foldr (fun e m => m.insert (e.2 % 2 ^ 64) (e.1 :: m.getD (e.2 % 2 ^ 64) [])) {}

theorem addrGroups_getD (l : List (String × Nat)) (a : Nat) :
    (addrGroups l).getD a [] = (l.filter fun e => e.2 % 2 ^ 64 == a).map (·.1) := by
  induction l with
  | nil => simp [addrGroups]
  | cons e l ih =>
    simp only [addrGroups, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : e.2 % 2 ^ 64 = a
    · simp [h, ih]
    · have h' : (e.2 % 2 ^ 64 == a) = false := by simpa using h
      simp [h', ih]

theorem addrs_all_eq (l : List (String × Nat)) (n : String) (a : Nat) :
    (l.all fun e => e.1 == n || e.2 % 2 ^ 64 != a) = ((addrGroups l).getD a []).all (· == n) := by
  rw [addrGroups_getD, List.all_map, List.all_filter]
  congr 1
  funext e
  cases h1 : (e.1 == n) <;> cases h2 : (e.2 % 2 ^ 64 == a) <;> simp_all

/-! ## The context -/

/-- **What `linkChks` and `globalChks` look up**, computed once (`LinkCtx.of`). -/
structure LinkCtx where
  /-- the CLIF image's symbols (`I.syms.lookup`) -/
  S : String → Option Nat
  /-- the program's functions (`P.func?`) -/
  F : String → Option Clif.Function
  /-- the link map (`I.addrs.lookup`) -/
  A : String → Option Nat
  /-- the link map's names by address (`addrGroups I.addrs`) -/
  G : Std.HashMap Nat (List String)
  /-- the names the program declares (`calleeSet P`) -/
  callees : Std.HashSet String
  /-- a function of the program has an indirect call -/
  anyInd : Bool
  /-- the table's code ranges -/
  ents : List RaEnt

/-- The context of the checks of `I`'s program `P` with compiled table `T`. -/
def LinkCtx.of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) : LinkCtx :=
  let sy := assocMap I.syms
  let fm := funcMap P
  let am := assocMap I.addrs
  { S := fun n => sy[n]?, F := fun n => fm[n]?, A := fun n => am[n]?, G := addrGroups I.addrs,
    callees := calleeSet P, anyInd := P.funcs.any (!indFreeB ·), ents := T.map RaEnt.of }

/-- **`linkChks` with the context `C`** (`linkChksWith_of`). -/
def linkChksWith (C : LinkCtx) (P : Clif.Program) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  -- `g`'s facts bound before the scans over the program (a closure `indToFastB C.S g` of a
  -- definition with the `let`s inside is eta-expanded and recomputes them per call)
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOk C.F P g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallFastB C.ents g a),
   ("indScope/indSig", indFastB P C.S g)]

theorem linkChksWith_of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) :
    linkChksWith (LinkCtx.of I P T) P g r = linkChks I P T g r := by
  simp only [linkChksWith, LinkCtx.of, assocMap_fun, funcMap_fun, indToWithB_declSet, indFastB_eq,
    calleeSet_contains, raCallFastB_eq, siteWithOk_func?]
  rfl

/-- `addrSlotsB` with the program's functions looked up through `F`. -/
def addrSlotsWithB (F : String → Option Clif.Function) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (S : String → Option Nat) : Bool :=
  !(T.any (fun e => (RAFrame.compute e.2.vcp e.2.rf).intBase != 0) && P.funcs.any (!indFreeB ·)) ||
    P.funcs.all (fun h => (S h.name).isNone || h.slots.isEmpty) ||
    P.funcs.any fun g => g.externs.any fun e => match F e.2.name with
      | some h => !h.slots.isEmpty
      | none => false

/-- **`globalChks` with the context `C`** (`globalChksWith_of`). -/
def globalChksWith (C : LinkCtx) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) : List (String × Bool) :=
  [("names: distinct", decide (P.funcs.map (·.name)).Nodup),
   ("imgCode: the image reads back", imgB T),
   ("raStar", raStarB T (BitVec.ofNat 64 I.raStar)),
   ("symInj", P.funcs.all fun h => let a := (C.A h.name).getD 0
      decide (a < 2 ^ 64) && a != 0 && (C.G.getD a []).all (· == h.name)),
   ("symOk", I.syms.all fun e => (C.A e.1).getD 0 == e.2),
   ("addrSlots", addrSlotsWithB C.F P T C.S)]

theorem globalChksWith_of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) :
    globalChksWith (LinkCtx.of I P T) I P T = globalChks I P T := by
  simp only [globalChksWith, LinkCtx.of, assocMap_fun, funcMap_fun, ← addrs_all_eq]
  rfl

end E2E.LinkCheck
