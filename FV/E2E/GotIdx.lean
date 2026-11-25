import FV.E2E.LinkIdxT
import FV.E2E.ReturnPinCheckIdx

/-! # The GOT symbols of a function's call sites, indexed once per function (#1090)

`gotOf vc t` (`FV/E2E/GotFlow.lean`), the GOT symbol a call through the vreg `t` enters, scans the
whole VCode `vc`: the first `loadExtNameGot` into `t` (`gotSym`), then every instruction's operands
and every call site of every block (`gotB`). The link checks evaluate it at every `blr` site, and
the `blr` checks once per function of the program the site may enter (`blrOk`, `blrOkTC`,
`blrOkC`) and once per site in the return-pin check (`returnPinsIdx`): sites × instructions steps
per function at least. num-bigint 0.5.1's `bigint_scalar` test executable (debug; its function
`test_scalar_div_rem#1::check_sub`: 31,015 instructions, 3,119 `try_call`s) did not finish
`link-check` in 3 h 50 min, all of it in these scans (#1090).

`GotIdx.of vc` builds, in one pass over `vc`, the first GOT symbol of each vreg (`lookupMap`), the
instructions defining each vreg and the call sites through each vreg (`groupMulti`); `GotIdx.got`
decides `gotB` only on those (`GotIdx.got_of`: the same answer as `gotOf`), and `GotIdx.tab` keeps
the vregs it accepts (`GotIdx.tab_get`). The link checks with the table built once per function
(`linkChksWithIG`, `linkChksWithTIG`, `linkChksWithTSIG`, `returnPinsIdxG`), and with the functions
their `blr` sites may enter filtered once per function (`progMay`), are equal to
`linkChksWithI`, `linkChksWithTI`, `linkChksWithTSI`, `returnPinsIdx` (`@[csimp]`
`linkChksWithI_eq_got`, …), which `link-check` evaluates. No statement changes.
-/

namespace E2E

open Backend

/-- `l` as a hash map; the first entry of a key wins (`List.lookup`'s answer: `lookupMap_get`). -/
def lookupMap {K V : Type} [BEq K] [Hashable K] (l : List (K × V)) : Std.HashMap K V :=
  l.foldr (fun p m => m.insert p.1 p.2) {}

theorem lookupMap_get {K V : Type} [BEq K] [Hashable K] [LawfulBEq K] (l : List (K × V)) (k : K) :
    (lookupMap l)[k]? = l.lookup k := by
  induction l with
  | nil => simp [lookupMap]
  | cons p l ih =>
    obtain ⟨a, v⟩ := p
    simp only [lookupMap, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons]
    by_cases h : a = k
    · subst h; simp
    · have h' : (k == a) = false := by simpa using Ne.symm h
      simp [h, h']

/-- The GOT load of an instruction: `(t, n)` for `loadExtNameGot (.vreg t .int) n`. -/
def gotPair : MInst → Option (Nat × String)
  | .loadExtNameGot (.vreg t .int) n => some (t, n)
  | _ => none

/-- The vregs an instruction defines (its def operands; none where its operands are not
computed, where `gotDefB` holds). -/
def defVregs (i : MInst) : List Nat :=
  match i.operands with
  | .ok ops => (ops.toList.filter (·.isDef)).map (·.vreg)
  | .error _ => []

/-- The vreg a call or `try_call` goes through: `t` for the destination `.reg (.vreg t .int)`. -/
def callVreg : MInst → Option Nat
  | .call info | .tryCall info _ => match info.dest with
    | .reg (.vreg t .int) => some t
    | _ => none
  | _ => none

/-- The instructions of `vc`, block by block. -/
def vcInsts (vc : VCode) : List MInst := vc.blocks.toList.flatMap (·.insts.toList)

/-- The positions of `vc`: each block with each index of its instructions. -/
def vcSites (vc : VCode) : List (VBlock × Nat) :=
  vc.blocks.toList.flatMap fun vb => (List.range vb.insts.size).map (vb, ·)

/-- **The GOT facts of a VCode, indexed by vreg**: the symbol of the first GOT load into each
vreg, the instructions defining each vreg, and the call sites through each vreg. -/
structure GotIdx where
  syms : Std.HashMap Nat String
  defs : Std.HashMap Nat (List MInst)
  sites : Std.HashMap Nat (List (VBlock × Nat))

/-- The index of `vc`, built in one pass over its instructions. -/
def GotIdx.of (vc : VCode) : GotIdx where
  syms := lookupMap ((vcInsts vc).filterMap gotPair)
  defs := LinkCheck.groupMulti defVregs (vcInsts vc)
  sites := LinkCheck.groupMulti (fun p => (p.1.insts[p.2]?.bind callVreg).toList) (vcSites vc)

/-- `gotB vc t n` on the index: the instructions defining `t` and the calls through `t`. -/
def GotIdx.ok (X : GotIdx) (t : Nat) (n : String) : Bool :=
  (X.defs.getD t []).all (gotDefB t n) && (X.sites.getD t []).all fun p => gotSiteB t n p.1 p.2

/-- `gotOf` on the index (`GotIdx.got_of`). -/
def GotIdx.got (X : GotIdx) (t : Nat) : Option String :=
  match X.syms[t]? with
  | some n => if X.ok t n then some n else none
  | none => none

/-- The vregs with a GOT symbol (`GotIdx.tab_get`): `gotOf`'s answers as a hash map. -/
def GotIdx.tab (X : GotIdx) : Std.HashMap Nat String := X.syms.filter X.ok

private theorem lookup_filterMap_gotPair (t : Nat) :
    ∀ l : List MInst, (l.filterMap gotPair).lookup t =
      l.findSome? fun i => (gotPair i).bind fun p => if p.1 = t then some p.2 else none
  | [] => rfl
  | i :: l => by
    rw [List.filterMap_cons, List.findSome?_cons]
    cases hp : gotPair i with
    | none => exact lookup_filterMap_gotPair t l
    | some p =>
      obtain ⟨t', n⟩ := p
      simp only [Option.bind_some, List.lookup_cons]
      by_cases h : t' = t
      · subst h; simp
      · have h' : (t == t') = false := by simpa using Ne.symm h
        simp only [h', h, ite_false]
        exact lookup_filterMap_gotPair t l

theorem GotIdx.syms_of (vc : VCode) (t : Nat) : (GotIdx.of vc).syms[t]? = gotSym vc t := by
  simp only [GotIdx.of, lookupMap_get, vcInsts]
  unfold gotSym
  rw [lookup_filterMap_gotPair]
  congr 1
  funext i
  cases i <;> try rfl
  rename_i rd n
  cases rd <;> try rfl
  rename_i t' c
  cases c <;> rfl

/-- `gotB` as a scan over the instructions and one over the positions. -/
theorem gotB_flat (vc : VCode) (t : Nat) (n : String) :
    gotB vc t n = ((vcInsts vc).all (gotDefB t n) &&
      (vcSites vc).all fun p => gotSiteB t n p.1 p.2) := by
  apply Bool.eq_iff_iff.2
  simp only [gotB, vcInsts, vcSites, ← Array.all_toList, List.all_flatMap, List.all_map,
    Function.comp_def, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro h
    exact ⟨fun vb hvb => (h vb hvb).1, fun vb hvb => (h vb hvb).2⟩
  · intro h vb hvb
    exact ⟨h.1 vb hvb, h.2 vb hvb⟩

theorem defVregs_of_gotDefB {t : Nat} {n : String} {i : MInst} (h : gotDefB t n i = false) :
    t ∈ defVregs i := by
  unfold gotDefB at h
  unfold defVregs
  split at h
  · rename_i ops hops
    rw [hops]
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Array.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨j, hj, hd, hv⟩, -⟩ := h
    simp only [List.mem_map, List.mem_filter]
    exact ⟨ops[j], ⟨Array.getElem_mem_toList hj, hd⟩, hv⟩
  · cases h

theorem callVreg_of_gotSiteB {t : Nat} {n : String} {vb : VBlock} {k : Nat}
    (h : gotSiteB t n vb k = false) : vb.insts[k]?.bind callVreg = some t := by
  unfold gotSiteB at h
  split at h
  · rename_i info hk
    rw [hk]
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
    simp [callVreg, h.1]
  · rename_i info ti hk
    rw [hk]
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
    simp [callVreg, h.1]
  · cases h

theorem GotIdx.ok_of (vc : VCode) (t : Nat) (n : String) :
    (GotIdx.of vc).ok t n = gotB vc t n := by
  rw [gotB_flat]
  unfold GotIdx.ok GotIdx.of
  simp only
  congr 1
  · symm
    apply LinkCheck.all_sub_eq
    · intro i hi hf
      exact (LinkCheck.mem_groupMulti _ _ _ _).2 ⟨hi, defVregs_of_gotDefB hf⟩
    · intro i hi
      exact ((LinkCheck.mem_groupMulti _ _ _ _).1 hi).1
  · symm
    apply LinkCheck.all_sub_eq
    · intro p hp hf
      refine (LinkCheck.mem_groupMulti _ _ _ _).2 ⟨hp, ?_⟩
      simp only [callVreg_of_gotSiteB hf, Option.toList_some, List.mem_singleton]
    · intro p hp
      exact ((LinkCheck.mem_groupMulti _ _ _ _).1 hp).1

/-- **The index decides `gotOf`.** -/
theorem GotIdx.got_of (vc : VCode) (t : Nat) : (GotIdx.of vc).got t = gotOf vc t := by
  unfold GotIdx.got gotOf
  rw [GotIdx.syms_of]
  cases gotSym vc t with
  | none => rfl
  | some n => simp only [GotIdx.ok_of]

theorem GotIdx.tab_get (X : GotIdx) (t : Nat) : X.tab[t]? = X.got t := by
  unfold GotIdx.tab GotIdx.got
  rw [Std.HashMap.getElem?_filter']
  cases X.syms[t]? with
  | none => rfl
  | some n => simp only [Option.filter_some]

/-- **`gotOf vc` through the table built once** (`GotIdx.of`, `GotIdx.tab`). -/
theorem gotOf_eq_tab (vc : VCode) : gotOf vc = fun t => (GotIdx.of vc).tab[t]? := by
  funext t
  rw [GotIdx.tab_get, GotIdx.got_of]

namespace LinkCheck

open Backend.Proof Backend.Proof.Driver

/-! ## The link checks with the GOT symbols of the function's table -/

/-- `siteWithOk` with the GOT symbols `got` (`siteWithOk_got`). -/
def siteWithOkG (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (got : Nat → Option String) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => true
  | .reg _ => blrOk P may got info

theorem siteWithOk_got (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode) :
    siteWithOk F P g may vc = siteWithOkG F P g may (gotOf vc) := rfl

/-- `siteWithOkTC` with the GOT symbols `got` (`siteWithOkTC_got`). -/
def siteWithOkTCG (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (got : Nat → Option String) (info : CallInfo) : Bool :=
  siteWithOkG F P g may got info ||
    match info.dest with
    | .reg (.vreg t .int) =>
      match info.uses.all fun u => u.1.isVirtual = true with
      | true =>
        match info.defs.all fun d => d.2.isVirtual = true with
        | true =>
          P.funcs.all fun h => !may h ||
            (match got t with | some n => h.name != n | none => false)
        | false => false
      | false => false
    | _ => false

theorem siteWithOkTC_got (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode) :
    siteWithOkTC F P g may vc = siteWithOkTCG F P g may (gotOf vc) := rfl

/-- `siteWithOkC` with the GOT symbols `got` (`siteWithOkC_got`). -/
def siteWithOkCG (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (got : Nat → Option String) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        (info.uses.all fun u => u.1.isVirtual = true) &&
        (info.defs.all fun d => d.2.isVirtual = true) &&
        decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs
    | none => true
  | .reg _ => blrOkC P may got info

theorem siteWithOkC_got (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode) :
    siteWithOkC F P g may vc = siteWithOkCG F P g may (gotOf vc) := rfl

/-! ## The functions a `blr` site may enter, filtered once per function

At each `blr` site, `blrOk`, `blrOkC` and `siteWithOkTCG` test `may h` for every function `h` of
the program they are given, although `may` does not depend on the site; `may` (`indToWithB`)
scans `g`'s externs (`gotDeclB`). num-bigint 0.5.1's `bigint_scalar` (debug), function
`check_sub`: 1,856 `blr` sites × 3,117 candidates × 3,771 externs, 209-233 s per evaluation of
its `blr` checks; `may` over the candidates once: 0.115 s (#1090). `progMay P may` keeps the
functions `may` admits, once per function; the site checks on it with `may := fun _ => true` are
the checks on `P` with `may` (`blrOk_may`, `blrOkC_may`, `siteWithOkG_may`, `siteWithOkCG_may`,
`siteWithOkTCG_may`). -/

/-- The functions of `P` that `may` admits. -/
def progMay (P : Clif.Program) (may : Clif.Function → Bool) : Clif.Program :=
  { P with funcs := P.funcs.filter may }

theorem all_filter_may {α : Type} (l : List α) (may p : α → Bool) :
    (l.filter may).all p = l.all fun h => !may h || p h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, List.all_cons]
    cases hm : may a <;> simp [ih]

theorem blrOk_may (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String)
    (info : CallInfo) : blrOk (progMay P may) (fun _ => true) got info = blrOk P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrOk, progMay, Bool.not_true, Bool.false_or, all_filter_may, Bool.or_assoc]
    | _ => rfl

theorem blrOkC_may (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String)
    (info : CallInfo) :
    blrOkC (progMay P may) (fun _ => true) got info = blrOkC P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrOkC, progMay, Bool.not_true, Bool.false_or, all_filter_may, Bool.or_assoc]
    | _ => rfl

theorem siteWithOkG_may (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (got : Nat → Option String) :
    siteWithOkG F (progMay P may) g (fun _ => true) got = siteWithOkG F P g may got := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrOk_may P may got _

theorem siteWithOkCG_may (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (got : Nat → Option String) :
    siteWithOkCG F (progMay P may) g (fun _ => true) got = siteWithOkCG F P g may got := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrOkC_may P may got _

theorem siteWithOkTCG_may (F : String → Option Clif.Function) (P : Clif.Program)
    (g : Clif.Function) (may : Clif.Function → Bool) (got : Nat → Option String) :
    siteWithOkTCG F (progMay P may) g (fun _ => true) got = siteWithOkTCG F P g may got := by
  funext info
  simp only [siteWithOkTCG, siteWithOkG_may]
  congr 1
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int => simp only [progMay, Bool.not_true, Bool.false_or, all_filter_may]
    | _ => rfl

/-- **`linkChksWithI` with the function's GOT table built once** (`linkChksWithI_eq_got`), the
functions its `blr` sites may enter filtered once (`progMay`, `siteWithOkG_may`). -/
def linkChksWithIG (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  let Pm := progMay Pg may
  let G := (GotIdx.of a.vcp).tab
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkG C.F Pm g (fun _ => true) fun t => G[t]?))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithB Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

@[csimp] theorem linkChksWithI_eq_got : @linkChksWithI = @linkChksWithIG := by
  funext C X P g r
  simp only [linkChksWithI, linkChksWithIG, siteWithOkG_may, siteWithOk_got, GotIdx.tab_get,
    GotIdx.got_of]

/-- **`linkChksWithTI` with the function's GOT table built once** (`linkChksWithTI_eq_got`), the
functions its `blr` sites may enter filtered once (`progMay`, `siteWithOkTCG_may`). -/
def linkChksWithTIG (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  let Pm := progMay Pg may
  let G := (GotIdx.of a.vcp).tab
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkTCG C.F Pm g (fun _ => true) fun t => G[t]?))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithB Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

@[csimp] theorem linkChksWithTI_eq_got : @linkChksWithTI = @linkChksWithTIG := by
  funext C X P g r
  simp only [linkChksWithTI, linkChksWithTIG, siteWithOkTCG_may, siteWithOkTC_got, GotIdx.tab_get,
    GotIdx.got_of]

/-- **`linkChksWithTSI` with the function's GOT table built once** (`linkChksWithTSI_eq_got`), the
functions its `blr` sites may enter filtered once (`progMay`, `siteWithOkCG_may`). -/
def linkChksWithTSIG (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  let Pm := progMay Pg may
  let G := (GotIdx.of a.vcp).tab
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkCG C.F Pm g (fun _ => true) fun t => G[t]?))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithBC Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

@[csimp] theorem linkChksWithTSI_eq_got : @linkChksWithTSI = @linkChksWithTSIG := by
  funext C X P g r
  simp only [linkChksWithTSI, linkChksWithTSIG, siteWithOkCG_may, siteWithOkC_got, GotIdx.tab_get,
    GotIdx.got_of]

/-- **`returnPinsIdx` with the function's GOT table built once** (`returnPinsIdx_eq_got`). -/
def returnPinsIdxG (C : ReturnPinCtx) (Y : ReturnPinIdx) (g : Clif.Function) : Bool :=
  let Ds := declSet g
  let ind := indFreeB g
  let sigs := indSigs g
  let to := indToWithB C.symbols ind (fun n => Ds.contains n) sigs g
  let cands := g.externs.flatMap (fun x => Y.byName.getD x.2.name []) ++
    (if ind then [] else
      (sigs.map fun s => Clif.AbiParam.tys s.params).eraseDups.flatMap fun k => Y.byTys.getD k [])
  let vcp := (C.artifact g).vcp
  let G := (GotIdx.of vcp).tab
  allInsts vcp (siteB (returnPinSiteIdx C (fun n => Y.byName.getD n []) to cands fun t => G[t]?))

@[csimp] theorem returnPinsIdx_eq_got : @returnPinsIdx = @returnPinsIdxG := by
  funext C Y g
  simp only [returnPinsIdx, returnPinsIdxG, GotIdx.tab_get, GotIdx.got_of]

end LinkCheck

end E2E
