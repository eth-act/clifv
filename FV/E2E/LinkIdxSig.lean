import FV.E2E.LinkIdxT

/-! # The `blr` and indirect-call checks with the signatures indexed (#1108)

`linkChksWithTSI` (`FV/E2E/LinkIdxT.lean`) tests each `blr` site of `g` (`blrOkC`) and `g`'s
indirect-call scope (`indWithBC`) against `LinkIdx.cands g sigs`: the functions `g` declares and
every function with the parameter types of one of `g`'s indirect-call signatures `sigs`, once per
signature of `sigs` (one per `call_indirect`) and once per site. On ruint's test executable the
largest groups by parameter types hold 82,814, 55,027 and 51,125 of its 232,604 functions, so a
function with `k` indirect calls tests about `k` times that many functions at each of its sites.

Neither test reads more of a function it may enter through an address than its signature, and
the `blr` test at a call through the GOT only the functions of that name. So, per function `g`:

* `M1`: the functions named by `g`'s declarations (`X.byName`), tested as before;
* `sigIdx P S`: the program's distinct signatures of functions with a symbol, by parameter types
  (once per program); `sigCands`: those with the parameter types of one of `sigs`; `S2`/`S3`:
  those an indirect call of `g` matches (`indMatchSig`, `indSigMatchSig`): the signatures of the
  functions `g` may enter through an address without declaring them;
* at a `blr` through the GOT symbol `n`: the functions named `n` (`X.byName`).

`blrFastC_eq`, `indFastC_eq`: equal to `blrOkC`, `indWithBC` over the program;
`linkChksWithTSX_of`: `linkChksWithTSX C (LinkIdx.of P C.ents) (sigIdx P C.S) P g r =
linkChksWithTS C P g r`. No statement changes.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

/-! ## The program's distinct signatures with a symbol, by parameter types -/

/-- `s` added to the group of its parameter types in `m`, unless it is there. -/
def sigInto (m : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (s : Clif.Signature) :
    Std.HashMap (List Clif.Ty) (List Clif.Signature) :=
  let k := Clif.AbiParam.tys s.params
  let l := m.getD k []
  if l.contains s then m else m.insert k (s :: l)

theorem mem_sigInto (m : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (s t : Clif.Signature)
    (k : List Clif.Ty) :
    t ∈ (sigInto m s).getD k [] ↔ t ∈ m.getD k [] ∨ (t = s ∧ Clif.AbiParam.tys s.params = k) := by
  unfold sigInto
  simp only
  split
  · rename_i hc
    constructor
    · exact .inl
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · simpa using hc
  · rw [Std.HashMap.getD_insert]
    by_cases hk : Clif.AbiParam.tys s.params = k
    · subst hk
      simp [or_comm]
    · simp [hk]

/-- **The distinct signatures of the functions of `P` with a symbol, by parameter types**
(`mem_sigIdx`). -/
def sigIdx (P : Clif.Program) (S : String → Option Nat) :
    Std.HashMap (List Clif.Ty) (List Clif.Signature) :=
  P.funcs.foldl (fun m h => if (S h.name).isSome then sigInto m h.sig else m) {}

theorem mem_sigIdx_foldl (S : String → Option Nat) (t : Clif.Signature) (k : List Clif.Ty) :
    ∀ (l : List Clif.Function) (m : Std.HashMap (List Clif.Ty) (List Clif.Signature)),
      t ∈ (l.foldl (fun m h => if (S h.name).isSome then sigInto m h.sig else m) m).getD k [] ↔
        t ∈ m.getD k [] ∨
          ∃ h ∈ l, (S h.name).isSome = true ∧ h.sig = t ∧ Clif.AbiParam.tys t.params = k
  | [], m => by simp
  | h :: l, m => by
    rw [List.foldl_cons, mem_sigIdx_foldl S t k l]
    split
    · rename_i hs
      rw [mem_sigInto]
      constructor
      · rintro ((h1 | ⟨rfl, h2⟩) | ⟨h', hl, h3⟩)
        · exact .inl h1
        · exact .inr ⟨h, List.mem_cons_self, hs, rfl, h2⟩
        · exact .inr ⟨h', List.mem_cons_of_mem _ hl, h3⟩
      · rintro (h1 | ⟨h', hl, h3⟩)
        · exact .inl (.inl h1)
        · rcases List.mem_cons.1 hl with rfl | hl
          · obtain ⟨-, rfl, h4⟩ := h3
            exact .inl (.inr ⟨rfl, h4⟩)
          · exact .inr ⟨h', hl, h3⟩
    · rename_i hs
      constructor
      · rintro (h1 | ⟨h', hl, h3⟩)
        · exact .inl h1
        · exact .inr ⟨h', List.mem_cons_of_mem _ hl, h3⟩
      · rintro (h1 | ⟨h', hl, h3⟩)
        · exact .inl h1
        · rcases List.mem_cons.1 hl with rfl | hl
          · exact absurd h3.1 hs
          · exact .inr ⟨h', hl, h3⟩

theorem mem_sigIdx (P : Clif.Program) (S : String → Option Nat) (t : Clif.Signature)
    (k : List Clif.Ty) :
    t ∈ (sigIdx P S).getD k [] ↔
      ∃ h ∈ P.funcs, (S h.name).isSome = true ∧ h.sig = t ∧ Clif.AbiParam.tys t.params = k := by
  simp [sigIdx, mem_sigIdx_foldl]

/-- The signatures of `SI` with the parameter types of one of `sigs`. -/
def sigCands (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature))
    (sigs : List Clif.Signature) : List Clif.Signature :=
  (sigs.map fun s => Clif.AbiParam.tys s.params).eraseDups.flatMap fun k => SI.getD k []

theorem mem_sigCands {SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)}
    {sigs : List Clif.Signature} {t : Clif.Signature} :
    t ∈ sigCands SI sigs ↔ ∃ s ∈ sigs, t ∈ SI.getD (Clif.AbiParam.tys s.params) [] := by
  simp only [sigCands, List.mem_flatMap, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, ht⟩
    exact ⟨s, hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ht⟩

/-- `indMatchWithB sigs h` from `h`'s signature `t` (`indMatchWithB_sig`). -/
def indMatchSig (sigs : List Clif.Signature) (t : Clif.Signature) : Bool :=
  sigs.any fun s => s.abiMatch t && t.returns.length == s.returns.length

theorem indMatchWithB_sig (sigs : List Clif.Signature) (h : Clif.Function) :
    indMatchWithB sigs h = indMatchSig sigs h.sig := by
  simp only [indMatchWithB, indMatchSig, LinkSys.IndSigMatch]
  congr 1
  funext s
  by_cases hb : s.abiMatch h.sig = true <;> simp [hb]

/-- The first disjunct of `indSigWithB` from `h`'s signature `t`. -/
def indSigMatchSig (sigs : List Clif.Signature) (t : Clif.Signature) : Bool :=
  sigs.any fun s => s.abiMatch t

theorem indSigMatchSig_eq (sigs : List Clif.Signature) (h : Clif.Function) :
    (sigs.any fun s => decide (LinkSys.IndSigMatch s h)) = indSigMatchSig sigs h.sig := by
  simp only [indSigMatchSig, LinkSys.IndSigMatch]
  congr 1
  funext s
  by_cases hb : s.abiMatch h.sig = true <;> simp [hb]

theorem tys_of_abiMatch {s t : Clif.Signature} (h : s.abiMatch t = true) :
    Clif.AbiParam.tys t.params = Clif.AbiParam.tys s.params :=
  (Clif.Signature.abiMatch_eq_true.mp h).1.symm

/-! ## The `blr` sites -/

/-- `blrOkC`'s test of a function of signature `t` at the `blr` site `info`. -/
def blrSigB (info : CallInfo) (t : Clif.Signature) : Bool :=
  decide ((regLocs t).length ≠ info.uses.length) ||
    (decide (info.uses.map (·.2) = regLocs t) && defsOkC t info.defs)

/-- **`blrOkC` with the functions it tests precomputed** (`blrFastC_eq`): at a call through the
GOT symbol `n` the functions named `n` (`byName n`), at another `blr` the functions `g` declares
(`M1`) and the signatures `S2` of the others `g` may enter. -/
def blrFastC (byName : String → List Clif.Function) (may : Clif.Function → Bool)
    (M1 : List Clif.Function) (S2 : List Clif.Signature) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .reg (.vreg t .int) =>
    (info.uses.all fun u => u.1.isVirtual = true) && (info.defs.all fun d => d.2.isVirtual = true) &&
    match got t with
    | some n => (byName n).all fun h => !may h || blrSigB info h.sig
    | none => M1.all (fun h => !may h || blrSigB info h.sig) && S2.all (blrSigB info)
  | _ => false

theorem blrFastC_eq {P : Clif.Program} {byName : String → List Clif.Function}
    {may : Clif.Function → Bool} {M1 : List Clif.Function} {S2 : List Clif.Signature}
    (D : String → Bool)
    (hB : ∀ n h, h ∈ byName n ↔ h ∈ P.funcs ∧ h.name = n)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, may h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, may h = true → D h.name = false → h.sig ∈ S2)
    (got : Nat → Option String) (info : CallInfo) :
    blrFastC byName may M1 S2 got info = blrOkC P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrFastC, blrOkC]
        congr 1
        apply Bool.eq_iff_iff.2
        cases hg : got t with
        | some n =>
          simp only [List.all_eq_true]
          constructor
          · intro h x hx
            by_cases hn : x.name = n
            · have := h x ((hB n x).2 ⟨hx, hn⟩)
              cases hm : may x
              · simp
              · simp only [hm, Bool.not_true, Bool.false_or, blrSigB] at this
                simp only [hm, hn, bne_self_eq_false, Bool.not_true, Bool.false_or]
                exact this
            · simp [hn]
          · intro h x hx
            obtain ⟨hx', hn⟩ := (hB n x).1 hx
            have := h x hx'
            simp only [hn, bne_self_eq_false, Bool.or_false] at this
            cases hm : may x
            · simp
            · simp only [hm, Bool.not_true, Bool.false_or] at this
              simp only [Bool.not_true, Bool.false_or, blrSigB]
              exact this
        | none =>
          simp only [List.all_eq_true, Bool.and_eq_true]
          constructor
          · rintro ⟨h1, h2⟩ x hx
            cases hm : may x
            · simp
            · cases hd : D x.name
              · have := h2 _ (hS2 x hx hm hd)
                simp only [blrSigB] at this
                simp only [Bool.not_true, Bool.or_false, Bool.false_or]
                exact this
              · have := h1 x (hD x hx hd)
                simp only [hm, Bool.not_true, Bool.false_or, blrSigB] at this
                simp only [Bool.not_true, Bool.or_false, Bool.false_or]
                exact this
          · intro h
            refine ⟨fun x hx => ?_, fun t ht => ?_⟩
            · have := h x (hM1 x hx)
              cases hm : may x
              · simp
              · simp only [hm, Bool.not_true, Bool.or_false, Bool.false_or] at this
                simp only [Bool.not_true, Bool.false_or, blrSigB]
                exact this
            · obtain ⟨x, hx, hm, rfl⟩ := hS1 t ht
              have := h x hx
              simp only [hm, Bool.not_true, Bool.or_false, Bool.false_or] at this
              simp only [blrSigB]
              exact this
    | _ => rfl

/-- `siteWithOkC` with `blrFastC` at the `blr` sites (`siteFastC_eq`). -/
def siteFastC (F : String → Option Clif.Function) (g : Clif.Function)
    (byName : String → List Clif.Function) (may : Clif.Function → Bool)
    (M1 : List Clif.Function) (S2 : List Clif.Signature) (vc : VCode) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        (info.uses.all fun u => u.1.isVirtual = true) &&
        (info.defs.all fun d => d.2.isVirtual = true) &&
        decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs
    | none => true
  | .reg _ => blrFastC byName may M1 S2 (gotOf vc) info

theorem siteFastC_eq (F : String → Option Clif.Function) {P : Clif.Program} (g : Clif.Function)
    {byName : String → List Clif.Function} {may : Clif.Function → Bool}
    {M1 : List Clif.Function} {S2 : List Clif.Signature} (D : String → Bool)
    (hB : ∀ n h, h ∈ byName n ↔ h ∈ P.funcs ∧ h.name = n)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, may h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, may h = true → D h.name = false → h.sig ∈ S2) (vc : VCode) :
    siteFastC F g byName may M1 S2 vc = siteWithOkC F P g may vc := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrFastC_eq D hB hM1 hD hS1 hS2 _ _

/-! ## The indirect-call scope -/

/-- `indWithBC`'s bound on a function of signature `t`. -/
def indSigB8 (t : Clif.Signature) : Bool :=
  match sigParamBytes t with
  | .ok b => decide (b.length ≤ 8)
  | .error _ => false

/-- **`indWithBC` with the functions it tests precomputed** (`indFastC_eq`): the functions `g`
declares (`M1`, the test `q`) and the signatures `S3` of the others. -/
def indFastC (ind : Bool) (q : Clif.Function → Bool) (M1 : List Clif.Function)
    (S3 : List Clif.Signature) : Bool :=
  ind || (M1.all q && S3.all indSigB8)

theorem indFastC_eq {P : Clif.Program} {S : String → Option Nat} {ind : Bool}
    {D : String → Bool} {sigs : List Clif.Signature} {M1 : List Clif.Function}
    {S3 : List Clif.Signature}
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ind = false → ∀ t ∈ S3, ∃ h ∈ P.funcs,
      mayWithB S ind D h.name = true ∧ indSigWithB D sigs h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, mayWithB S ind D h.name = true → indSigWithB D sigs h = true →
      D h.name = false → h.sig ∈ S3) :
    indFastC ind (fun h => !mayWithB S ind D h.name || !indSigWithB D sigs h || indSigB8 h.sig)
      M1 S3 = indWithBC P S ind D sigs := by
  unfold indFastC indWithBC
  cases ind with
  | true => rfl
  | false =>
    have hS1 := hS1 rfl
    simp only [Bool.false_or]
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      cases hm : mayWithB S false D x.name
      · simp
      · cases hs : indSigWithB D sigs x
        · simp
        · cases hd : D x.name
          · have := h2 _ (hS2 x hx hm hs hd)
            simp only [indSigB8] at this
            simp only [Bool.not_true, Bool.false_or]
            exact this
          · have := h1 x (hD x hx hd)
            simp only [hm, hs, Bool.not_true, Bool.false_or] at this
            simp only [Bool.not_true, Bool.false_or]
            exact this
    · intro h
      refine ⟨fun x hx => h x (hM1 x hx), fun t ht => ?_⟩
      obtain ⟨x, hx, hm, hs, rfl⟩ := hS1 t ht
      have := h x hx
      simp only [hm, hs, Bool.not_true, Bool.false_or] at this
      simp only [indSigB8]
      exact this

/-! ## The checks -/

/-- **`linkChksWithTSI` with the signatures indexed** (`linkChksWithTSX_of`): `SI` the program's
distinct signatures with a symbol (`sigIdx P C.S`); `g`'s candidates computed once. -/
def linkChksWithTSX (C : LinkCtx) (X : LinkIdx)
    (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let ind := indFreeB g
  let may := indToWithB C.S ind (fun n => Ds.contains n) sigs g
  let M1 := g.externs.flatMap fun e => X.byName.getD e.2.name []
  let cs := if ind then [] else sigCands SI sigs
  let S2 := cs.filter (indMatchSig sigs)
  let S3 := cs.filter (indSigMatchSig sigs)
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteFastC C.F g (fun n => X.byName.getD n []) may
     M1 S2 a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indFastC ind (fun h => !mayWithB C.S ind (fun n => Ds.contains n) h.name ||
     !indSigWithB (fun n => Ds.contains n) sigs h || indSigB8 h.sig) M1 S3)]

theorem byName_mem (P : Clif.Program) (E : List RaEnt) (n : String) (h : Clif.Function) :
    h ∈ (LinkIdx.of P E).byName.getD n [] ↔ h ∈ P.funcs ∧ h.name = n := by
  simp only [LinkIdx.of, mem_groupMulti, List.mem_singleton]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b.symm⟩, fun ⟨a, b⟩ => ⟨a, b.symm⟩⟩

theorem M1_sub (P : Clif.Program) (E : List RaEnt) (g : Clif.Function) {h : Clif.Function}
    (hh : h ∈ g.externs.flatMap fun e => (LinkIdx.of P E).byName.getD e.2.name []) :
    h ∈ P.funcs := by
  obtain ⟨e, -, he⟩ := List.mem_flatMap.1 hh
  exact ((byName_mem P E _ h).1 he).1

theorem M1_decl (P : Clif.Program) (E : List RaEnt) (g : Clif.Function) {h : Clif.Function}
    (hh : h ∈ P.funcs) (hd : (declSet g).contains h.name = true) :
    h ∈ g.externs.flatMap fun e => (LinkIdx.of P E).byName.getD e.2.name [] := by
  have hd' : declB g h.name = true := by rw [← declSet_contains]; exact hd
  simp only [declB, List.any_eq_true, beq_iff_eq] at hd'
  obtain ⟨e, he, hen⟩ := hd'
  exact List.mem_flatMap.2 ⟨e, he, (byName_mem P E _ h).2 ⟨hh, hen.symm⟩⟩

/-- The two entries of `linkChksWithTSX` that differ from `linkChksWithTSI`'s, equal at the
indices of `P` (with `g`'s facts named). -/
theorem linkChksWithTSX_entries (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (D : String → Bool) (sigs : List Clif.Signature) (ind : Bool) (may : Clif.Function → Bool)
    (M1 : List Clif.Function) (cs : List Clif.Signature)
    (eD : D = fun n => (declSet g).contains n) (es : sigs = indSigs g) (ei : ind = indFreeB g)
    (em : may = indToWithB C.S ind D sigs g)
    (eM : M1 = g.externs.flatMap fun e => (LinkIdx.of P C.ents).byName.getD e.2.name [])
    (ec : cs = if ind = true then [] else sigCands (sigIdx P C.S) sigs) :
    siteFastC C.F g (fun n => (LinkIdx.of P C.ents).byName.getD n []) may M1
        (cs.filter (indMatchSig sigs)) =
      siteWithOkC C.F ((LinkIdx.of P C.ents).progFor P g sigs) g may ∧
    indFastC ind (fun h => !mayWithB C.S ind D h.name || !indSigWithB D sigs h || indSigB8 h.sig)
        M1 (cs.filter (indSigMatchSig sigs)) =
      indWithBC ((LinkIdx.of P C.ents).progFor P g sigs) C.S ind D sigs := by
  subst eD es ei em eM ec
  have hM1 := fun h (hh : h ∈ g.externs.flatMap fun e => (LinkIdx.of P C.ents).byName.getD e.2.name []) =>
    M1_sub P C.ents g hh
  have hD := fun h (hh : h ∈ P.funcs) (hd : (declSet g).contains h.name = true) =>
    M1_decl P C.ents g hh hd
  have hcs : ∀ t ∈ (if indFreeB g = true then [] else sigCands (sigIdx P C.S) (indSigs g)),
      indFreeB g = false ∧ ∃ h ∈ P.funcs, (C.S h.name).isSome = true ∧ h.sig = t := by
    intro t ht
    cases hi : indFreeB g
    · rw [hi] at ht
      simp only [Bool.false_eq_true, ite_false] at ht
      obtain ⟨s, -, hs⟩ := mem_sigCands.1 ht
      obtain ⟨h, hh, h1, h2, -⟩ := (mem_sigIdx P C.S t _).1 hs
      exact ⟨rfl, h, hh, h1, h2⟩
    · rw [hi] at ht; simp at ht
  have hcs2 : ∀ h ∈ P.funcs, indFreeB g = false → (C.S h.name).isSome = true →
      ∀ s ∈ indSigs g, s.abiMatch h.sig = true →
        h.sig ∈ (if indFreeB g = true then [] else sigCands (sigIdx P C.S) (indSigs g)) := by
    intro h hh hi hS s hs hm
    rw [hi]
    simp only [Bool.false_eq_true, ite_false]
    exact mem_sigCands.2 ⟨s, hs, (mem_sigIdx P C.S h.sig _).2
      ⟨h, hh, hS, rfl, tys_of_abiMatch hm⟩⟩
  have hmay : ∀ h, indToWithB C.S (indFreeB g) (fun n => (declSet g).contains n) (indSigs g) g h =
      true → (declSet g).contains h.name = false → indFreeB g = false ∧
        (C.S h.name).isSome = true ∧ indMatchWithB (indSigs g) h = true := by
    intro h hm hd
    simp only [indToWithB, mayWithB, hd, Bool.false_or, Bool.false_and, Bool.and_eq_true,
      Bool.not_eq_true'] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  constructor
  · funext vc
    rw [siteWithOkC_progFor]
    refine siteFastC_eq C.F g (fun n => (declSet g).contains n) (fun n h => byName_mem P C.ents n h)
      hM1 hD (fun t ht => ?_) (fun h hh hm hd => ?_) vc
    · obtain ⟨htc, hmt⟩ := List.mem_filter.1 ht
      obtain ⟨hi, h, hh, hS, rfl⟩ := hcs t htc
      refine ⟨h, hh, ?_, rfl⟩
      simp only [indToWithB, mayWithB, hi, hS, indMatchWithB_sig, hmt, Bool.or_true,
        Bool.not_false, Bool.true_and, Bool.and_true]
    · obtain ⟨hi, hS, hmw⟩ := hmay h hm hd
      rw [indMatchWithB_sig] at hmw
      refine List.mem_filter.2 ⟨?_, hmw⟩
      obtain ⟨s, hs, hsm⟩ := List.any_eq_true.1 hmw
      exact hcs2 h hh hi hS s hs (Bool.and_eq_true _ _ ▸ hsm).1
  · rw [indWithBC_progFor]
    refine indFastC_eq hM1 hD (fun hi t ht => ?_) (fun h hh hm hs hd => ?_)
    · obtain ⟨htc, hmt⟩ := List.mem_filter.1 ht
      obtain ⟨-, h, hh, hS, rfl⟩ := hcs t htc
      refine ⟨h, hh, ?_, ?_, rfl⟩
      · simp [mayWithB, hi, hS]
      · simp only [indSigWithB, indSigMatchSig_eq, hmt, Bool.true_or]
    · simp only [mayWithB, hd, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hm
      simp only [indSigWithB, indSigMatchSig_eq, hd, Bool.false_and, Bool.or_false] at hs
      refine List.mem_filter.2 ⟨?_, hs⟩
      obtain ⟨s, hsm, hab⟩ := List.any_eq_true.1 hs
      exact hcs2 h hh hm.1 hm.2 s hsm hab

theorem linkChksWithTSX_of (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    linkChksWithTSX C (LinkIdx.of P C.ents) (sigIdx P C.S) g r = linkChksWithTS C P g r := by
  rw [← linkChksWithTSI_of]
  obtain ⟨hb, hi⟩ := linkChksWithTSX_entries C P g _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  simp only [linkChksWithTSX, linkChksWithTSI, hb, hi]

end E2E.LinkCheck
