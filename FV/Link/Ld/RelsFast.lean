import FV.Link.Ld.RelsTotal

/-! # `relsInB` in linear time (A1, #409)

`relsInB` classifies each relocation's symbol (`tgtOf`) and place by the output sections holding
its section (`secsOf`: a scan of every output section's parts, per relocation). `relsInFastB`
reads the classification from a table built once (`secCls`: per input section, whether an output
section holds it, whether all of those are outside / inside the TLS template), and is `relsInB`
(`relsInFastB_eq`). `lake exe lean-link --ld` decides it.
-/

namespace Link.Ld

/-- The classification before any output section: held by none, all (vacuously) outside and
inside the TLS template. -/
def clsInit : Bool × Bool × Bool := (false, true, true)

/-- The classification after an output section `s` holding the part. -/
def clsUpd (s : OSec) (c : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (true, c.2.1 && !tlsName s, c.2.2 && tlsName s)

/-- One output section's parts recorded. -/
def clsSec (m : Std.HashMap SecId (Bool × Bool × Bool)) (s : OSec) : Std.HashMap SecId (Bool × Bool × Bool) :=
  s.parts.foldl (fun m p => match p with
    | .input t => m.insert t (clsUpd s (m.getD t clsInit))
    | _ => m) m

/-- **The classification of every input section** by the output sections holding it. -/
def secCls (sorted : Array OSec) : Std.HashMap SecId (Bool × Bool × Bool) := sorted.foldl clsSec {}

theorem clsUpd_idem (s : OSec) (c : Bool × Bool × Bool) : clsUpd s (clsUpd s c) = clsUpd s c := by
  obtain ⟨a, b, d⟩ := c
  simp only [clsUpd, Bool.and_assoc, Bool.and_self]

theorem clsSec_go (s : OSec) (t : SecId) : ∀ (l : List Part) (m : Std.HashMap SecId (Bool × Bool × Bool)),
    (l.foldl (fun m p => match p with
      | .input t => m.insert t (clsUpd s (m.getD t clsInit))
      | _ => m) m).getD t clsInit =
      if l.any (fun q => decide (q = Part.input t)) then clsUpd s (m.getD t clsInit) else m.getD t clsInit
  | [], m => by simp
  | p :: l, m => by
    rw [List.foldl_cons, clsSec_go s t l]
    cases p with
    | input t' =>
      simp only [Std.HashMap.getD_insert, List.any_cons, Part.input.injEq]
      by_cases ht : t' = t
      · subst ht
        cases l.any (fun q => decide (q = Part.input t')) <;> simp [clsUpd_idem]
      · have : (t' == t) = false := by simp [ht]
        simp only [this, Bool.false_eq_true, ↓reduceIte, ht, decide_false, Bool.false_or]
    | _ => rfl

theorem clsSec_getD (m : Std.HashMap SecId (Bool × Bool × Bool)) (s : OSec) (t : SecId) :
    (clsSec m s).getD t clsInit =
      if s.parts.toList.any (fun q => decide (q = Part.input t)) then clsUpd s (m.getD t clsInit)
      else m.getD t clsInit := by
  unfold clsSec
  rw [← Array.foldl_toList, clsSec_go]

/-- The classification over the output sections `L`, from `c`. -/
def clsStep (t : SecId) (c : Bool × Bool × Bool) (s : OSec) : Bool × Bool × Bool :=
  if s.parts.toList.any (fun q => decide (q = Part.input t)) then clsUpd s c else c

theorem secCls_go (t : SecId) : ∀ (L : List OSec) (m : Std.HashMap SecId (Bool × Bool × Bool)),
    (L.foldl clsSec m).getD t clsInit = L.foldl (clsStep t) (m.getD t clsInit)
  | [], _ => rfl
  | s :: L, m => by
    rw [List.foldl_cons, List.foldl_cons, secCls_go t L, clsSec_getD]
    rfl

theorem clsStep_foldl (t : SecId) : ∀ (L : List OSec) (c : Bool × Bool × Bool),
    L.foldl (clsStep t) c =
      (c.1 || !(L.filter fun s => s.parts.toList.any fun q => decide (q = .input t)).isEmpty,
       c.2.1 && (L.filter fun s => s.parts.toList.any fun q => decide (q = .input t)).all (!tlsName ·),
       c.2.2 && (L.filter fun s => s.parts.toList.any fun q => decide (q = .input t)).all tlsName)
  | [], c => by simp
  | s :: L, c => by
    rw [List.foldl_cons, clsStep_foldl t L]
    unfold clsStep
    cases h : s.parts.toList.any fun q => decide (q = Part.input t)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, h]
    · simp only [↓reduceIte, List.filter_cons, h, clsUpd, List.isEmpty_cons, List.all_cons]
      obtain ⟨a, b, d⟩ := c
      cases b <;> cases d <;> cases tlsName s <;> simp

/-- **The table's classification is `secsOf`'s.** -/
theorem secCls_getD (sorted : Array OSec) (t : SecId) :
    (secCls sorted).getD t clsInit =
      (!(secsOf sorted (.input t)).isEmpty, (secsOf sorted (.input t)).all (!tlsName ·),
        (secsOf sorted (.input t)).all tlsName) := by
  unfold secCls
  rw [← Array.foldl_toList, secCls_go, Std.HashMap.getD_empty, clsStep_foldl]
  simp [clsInit, secsOf]

/-- `tgtOf` with the output sections' classification read from `cls` (`secCls`). -/
def tgtOfF (st : St) (g : GcOut) (sorted : Array OSec) (cls : Std.HashMap SecId (Bool × Bool × Bool))
    (fi j : Nat) : Option Tgt :=
  let names := sorted.toList.map (·.name)
  match st.target fi j with
  | .sec t x _ =>
    if (g.live[t.1]?.bind (·[t.2]?)).getD false then
      if h : t.1 < st.files.size then
        let c := cls.getD t clsInit
        if t.2 < st.files[t.1].secs.size && decide (x ≤ st.files[t.1].secs[t.2]!.size) && c.1 then
          if c.2.1 then some (.img t x)
          else if c.2.2 then some (.tls x)
          else none
        else none
      else none
    else if (g.eh[t.1]!.findIdx? (·.sec == t.2)).isSome then some (.eh x) else none
  | .abs v => some (.abs v)
  | .common _ _ => some .common
  | .undef n w => if synthKnownB names n then some .synth else if w && !synthMaybeB n then some .weak else none

theorem tgtOfF_eq (st : St) (g : GcOut) (sorted : Array OSec) (fi j : Nat) :
    tgtOfF st g sorted (secCls sorted) fi j = tgtOf st g sorted fi j := by
  unfold tgtOfF tgtOf
  simp only [secCls_getD]
  rfl

/-- `secRelsB` with the classification read from `cls`. -/
def secRelsF (st : St) (g : GcOut) (B : Bnd) (sorted : Array OSec) (cls : Std.HashMap SecId (Bool × Bool × Bool))
    (t : SecId) : Bool :=
  let f := st.files[t.1]!
  let s := f.secs[t.2]!
  let pLo : Int := if (cls.getD t clsInit).2.1 then (B.base : Int) else 0
  s.type == shtNobits ||
    (decide (t.1 < st.files.size) && decide (t.2 < f.secs.size) && decide (s.off + s.size ≤ f.data.size) &&
      (f.relas t.2).all fun r => decide (r.off + relocWidth r.type ≤ s.size) &&
        match tgtOfF st g sorted cls t.1 r.sym with
        | some k => relCheckB B (al4B st.files) r.type k r.addend pLo B.top
            (some (t, r.off)) (al4B st.files t && r.off % 4 == 0)
        | none => false)

/-- `ehRelsB` with the classification read from `cls`. -/
def ehRelsF (st : St) (g : GcOut) (B : Bnd) (sorted : Array OSec) (cls : Std.HashMap SecId (Bool × Bool × Bool))
    (e : EhOut) : Bool :=
  (ehRelas g e).all fun r =>
    decide (e.piece.off ≤ r.off ∧ r.off + relocWidth r.type ≤ e.piece.off + e.piece.size) &&
    match tgtOfF st g sorted cls e.file r.sym with
    | some k => relCheckB B (al4B st.files) r.type k r.addend 0 (B.top + B.eh) none false
    | none => false

/-- **`relsInB` with the classification table** (`relsInFastB_eq`). -/
def relsInFastB (o : Opts) (st : St) (g : GcOut) : Bool :=
  let D := layDecide st g
  let sorted := sortOSecs st.files D.osecs
  let B := bndOf o st g
  let cls := secCls sorted
  dOkB D sorted && D.ehs.all (ehRelsF st g B sorted cls) &&
    sorted.all fun s => s.parts.all fun p => match p with
      | .input t => secRelsF st g B sorted cls t
      | _ => true

theorem relsInFastB_eq (o : Opts) (st : St) (g : GcOut) : relsInFastB o st g = relsInB o st g := by
  unfold relsInFastB relsInB secRelsF ehRelsF secRelsB ehRelsB
  simp only [tgtOfF_eq, secCls_getD]
  rfl

end Link.Ld
