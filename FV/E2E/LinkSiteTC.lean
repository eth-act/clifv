import FV.E2E.LinkCheck
import FV.E2E.LinkCheckFast
import FV.E2E.CalleeWith
import FV.Link.DeadCleanupImage
import FV.Backend.Proof.IselCtlCallF

/-! # The call-site checks with typed `try_call`s (S11e6, #419)

`blrOkTC`/`siteOkTC`/`linkChksT`: the link checker's call-site conditions widened to admit a
`blr` site whose def targets are vregs of either class, provided the `blr` enters no function of
`P` (`blrOkTC`'s extra disjunct: for every function `may` lets it enter, the GOT symbol differs)
— a `try_call`'s callee is external (`InSubsetTC.tryExterns`), so the base contract covers it.
`blrOkTC_sound`: `blrOk`'s conclusion, or the entering-no-function fact. The machine-level
lemmas (`callRegs_eq_regC`, `call_useVals_regC`, …) are the class-generic forms of
`LinkArm.lean`'s for `argPairsC`/`callDefsC` calls.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The machine-level class-generic call lemmas -/

theorem call_zipC {L : List (Nat × RegClass × Reg)} {D : List (Reg × Nat × RegClass)}
    {regs : Array Reg} (hr : regs.toList = L.map (·.2.2) ++ D.map (·.1)) :
    ((retOpsC L ++ callDefOpsC D).toArray.zip regs).toList =
      (retOpsC L).zip (L.map (·.2.2)) ++ (callDefOpsC D).zip (D.map (·.1)) := by
  rw [Array.toList_zip, hr, List.toList_toArray, List.zip_append (by simp [retOpsC])]

theorem map_zip_retOpsC (s : Arm.ArmState) : ∀ L : List (Nat × RegClass × Reg),
    ((retOpsC L).zip (L.map (·.2.2))).map (fun p => regVal s p.2) =
      L.map (fun q => regVal s q.2.2)
  | [] => rfl
  | q :: L => by
    have := map_zip_retOpsC s L
    simp only [retOpsC, List.map_cons, List.zip_cons_cons] at this ⊢
    rw [this]

theorem retOpsC_isUse {L : List (Nat × RegClass × Reg)} {o : Operand} (h : o ∈ retOpsC L) :
    o.isUse = true := by
  simp only [retOpsC, List.mem_map] at h
  obtain ⟨q, -, rfl⟩ := h
  simp [Operand.isUse]

theorem callDefOpsC_not_isUse {D : List (Reg × Nat × RegClass)} {o : Operand}
    (h : o ∈ callDefOpsC D) : o.isUse = false := by
  simp only [callDefOpsC, List.mem_map] at h
  obtain ⟨q, -, rfl⟩ := h
  simp [Operand.isUse]

theorem callDefOpsC_isDef {D : List (Reg × Nat × RegClass)} {o : Operand}
    (h : o ∈ callDefOpsC D) : o.isDef = true := by
  simp only [callDefOpsC, List.mem_map] at h
  obtain ⟨q, -, rfl⟩ := h
  simp [Operand.isDef]

theorem retOpsC_not_isDef {L : List (Nat × RegClass × Reg)} {o : Operand} (h : o ∈ retOpsC L) :
    o.isDef = false := by
  simp only [retOpsC, List.mem_map] at h
  obtain ⟨q, -, rfl⟩ := h
  simp [Operand.isDef]

theorem call_useValsC {L : List (Nat × RegClass × Reg)} {D : List (Reg × Nat × RegClass)}
    {regs : Array Reg} (hr : regs.toList = L.map (·.2.2) ++ D.map (·.1)) (s : Arm.ArmState) :
    useVals (retOpsC L ++ callDefOpsC D).toArray regs s = L.map (fun q => regVal s q.2.2) := by
  simp only [useVals, call_zipC hr, List.filter_append]
  rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
  · rw [List.append_nil]; exact map_zip_retOpsC s L
  · intro p hp
    have := callDefOpsC_not_isUse (List.of_mem_zip hp).1
    rw [show p.fst.isUse = false from this]; simp
  · intro p hp
    exact retOpsC_isUse (List.of_mem_zip hp).1

theorem call_defsC {L : List (Nat × RegClass × Reg)} {D : List (Reg × Nat × RegClass)}
    {regs : Array Reg} (hr : regs.toList = L.map (·.2.2) ++ D.map (·.1)) :
    ((retOpsC L ++ callDefOpsC D).toArray.zip regs).toList.filter (·.1.isDef) =
      (callDefOpsC D).zip (D.map (·.1)) := by
  rw [call_zipC hr, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
  · rfl
  · intro p hp
    exact callDefOpsC_isDef (List.of_mem_zip hp).1
  · intro p hp
    have := retOpsC_not_isDef (List.of_mem_zip hp).1
    rw [show p.fst.isDef = false from this]; simp

theorem callRegs_eqC {L : List (Nat × RegClass × Reg)} {D : List (Reg × Nat × RegClass)}
    {regs : Array Reg}
    (hsz : (retOpsC L ++ callDefOpsC D).length = regs.size)
    (hfix : ∀ p ∈ ((retOpsC L ++ callDefOpsC D).toArray.zip (regs.map Loc.reg)).toList, ∀ r,
      p.1.con = .fixed r → p.2 = .reg r) :
    regs.toList = L.map (·.2.2) ++ D.map (·.1) := by
  apply zip_fixed (retOpsC L ++ callDefOpsC D) regs.toList _ (by simpa using hsz)
    (by simp [retOpsC, callDefOpsC])
  · intro i o r ho hr
    rw [List.getElem?_append] at ho hr
    simp only [retOpsC, callDefOpsC, List.length_map] at ho hr
    split at ho
    · rw [if_pos (by assumption)] at hr
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ho hr
      obtain ⟨q, hq, rfl⟩ := ho
      obtain ⟨q', hq', rfl⟩ := hr
      rw [hq] at hq'; cases hq'; rfl
    · rw [if_neg (by assumption)] at hr
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ho hr
      obtain ⟨q, hq, rfl⟩ := ho
      obtain ⟨q', hq', rfl⟩ := hr
      rw [hq] at hq'; cases hq'; rfl
  · intro p hp r hr
    exact hfix p (by simpa using hp) r hr

theorem callRegs_eq_regC {tv : Nat} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {regs : Array Reg}
    (hsz : (tgtOp tv :: (retOpsC L ++ callDefOpsC D)).length = regs.size)
    (hfix : ∀ p ∈ ((tgtOp tv :: (retOpsC L ++ callDefOpsC D)).toArray.zip (regs.map Loc.reg)).toList,
      ∀ r, p.1.con = .fixed r → p.2 = .reg r) :
    ∃ r0, regs.toList = r0 :: (L.map (·.2.2) ++ D.map (·.1)) := by
  obtain ⟨l⟩ := regs
  cases l with
  | nil => simp at hsz
  | cons r0 rs =>
    refine ⟨r0, ?_⟩
    have := callRegs_eqC (regs := rs.toArray) (by simpa using hsz) (fun p hp r hr => hfix p (by
      simp only [Array.toList_zip, List.toList_toArray, Array.toList_map, List.map_cons,
        List.zip_cons_cons, List.mem_cons] at hp ⊢
      exact .inr hp) r hr)
    simpa using this

theorem call_useVals_regC {tv : Nat} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {regs : Array Reg} {r0 : Reg}
    (hr : regs.toList = r0 :: (L.map (·.2.2) ++ D.map (·.1))) (s : Arm.ArmState) :
    useVals (tgtOp tv :: (retOpsC L ++ callDefOpsC D)).toArray regs s =
      regVal s r0 :: L.map (fun q => regVal s q.2.2) := by
  have h2 : regs = (r0 :: (L.map (·.2.2) ++ D.map (·.1))).toArray := by
    rw [← hr]
  have hrest := call_useValsC (L := L) (D := D)
    (regs := (L.map (·.2.2) ++ D.map (·.1)).toArray) (by simp) s
  rw [h2]
  simp only [useVals, Array.toList_zip, List.toList_toArray, List.zip_cons_cons, List.filter_cons,
    show (tgtOp tv).isUse = true from rfl, ↓reduceIte, List.map_cons] at hrest ⊢
  rw [hrest]

theorem call_defs_regC {tv : Nat} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {regs : Array Reg} {r0 : Reg}
    (hr : regs.toList = r0 :: (L.map (·.2.2) ++ D.map (·.1))) :
    ((tgtOp tv :: (retOpsC L ++ callDefOpsC D)).toArray.zip regs).toList.filter (·.1.isDef) =
      (callDefOpsC D).zip (D.map (·.1)) := by
  have h2 : regs = (r0 :: (L.map (·.2.2) ++ D.map (·.1))).toArray := by
    rw [← hr]
  have hrest := call_defsC (L := L) (D := D)
    (regs := (L.map (·.2.2) ++ D.map (·.1)).toArray) (by simp)
  rw [h2]
  simp only [Array.toList_zip, List.toList_toArray, List.zip_cons_cons, List.filter_cons,
    show (tgtOp tv).isDef = false from rfl, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
  exact hrest

/-! ## The widened call-site checks -/

/-- **`blrOk` with typed `try_call`s**: `blrOk`, or a `blr` through the GOT that enters no
function of `P` (`may` admits none with the GOT symbol's name) — a typed `try_call`'s callee is
external, so the base's contract covers the site. -/
def blrOkTC (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  blrOk P may got info ||
    match info.dest with
    | .reg (.vreg t .int) =>
      P.funcs.all fun h => !may h ||
        (match got t with | some n => h.name != n | none => false)
    | _ => false

/-- **Soundness of the widened `blr` check**: `blrOk`'s conclusion, or the `blr` enters no
function of `P`. -/
theorem blrOkTC_sound {P : Clif.Program} {may : Clif.Function → Bool} {got : Nat → Option String}
    {info : CallInfo} (h : blrOkTC P may got info = true) :
    (∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) →
        (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x) ∨
    (∃ t, info.dest = .reg (.vreg t .int) ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) → False) := by
  unfold blrOkTC at h
  cases hb : blrOk P may got info with
  | true =>
    rcases blrOk_sound hb with ⟨t, Lu, Ld, heq, hall⟩
    exact .inl ⟨t, Lu, Ld, heq, hall⟩
  | false =>
    rw [hb, Bool.false_or] at h
    rcases hd : info.dest with ⟨n⟩ | ⟨r⟩
    · rw [hd] at h; simp at h
    · rcases hr : r with ⟨t, c⟩ | ⟨n⟩ | _ | _ | ⟨n⟩
      · rcases c with _ | _
        · refine .inr ⟨t, rfl, fun hh hmem hm hgot => ?_⟩
          rw [hd, hr] at h
          have hall : P.funcs.all
              (fun hh => !may hh ||
                match got t with | some n => hh.name != n | none => false) = true := h
          have h1 := List.all_eq_true.mp hall hh hmem
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
          cases hg : got t
          · rw [hg] at h1
            simp only [Bool.false_or, reduceCtorEq] at h1
            rcases h1 with h2 | h2
            · rw [h2] at hm; simp at hm
            · exact h2.elim
          · rw [hg] at h1
            simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
            rcases h1 with h2 | h2
            · rw [h2] at hm; exact Bool.noConfusion hm
            · exact absurd (hgot _ hg) h2
        · rw [hd, hr] at h; simp at h
      · rw [hd, hr] at h; simp at h
      · rw [hd, hr] at h; simp at h
      · rw [hd, hr] at h; simp at h
      · rw [hd, hr] at h; simp at h

/-- `siteOk` with the widened `blr` check. -/
def siteOkTC (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode)
    (info : CallInfo) : Bool :=
  siteOk P g may vc info ||
    match info.dest with
    | .reg (.vreg t .int) =>
      P.funcs.all fun h => !may h ||
        (match gotOf vc t with | some n => h.name != n | none => false)
    | _ => false

theorem blrOkTC_of_blrOk {P : Clif.Program} {may : Clif.Function → Bool}
    {got : Nat → Option String} {info : CallInfo} (h : blrOk P may got info = true) :
    blrOkTC P may got info = true := by
  unfold blrOkTC
  rw [h, Bool.true_or]

/-- `siteOk` implies `siteOkTC` (the widened check only adds cases). -/
theorem siteOk_le_siteOkTC {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : siteOk P g may vc info = true) :
    siteOkTC P g may vc info = true := by
  unfold siteOkTC
  rw [Bool.or_eq_true]
  cases info.dest with
  | reg r => exact .inl h
  | sym n => exact .inl h

theorem siteB_mono {q q' : CallInfo → Bool}
    (hle : ∀ info, q info = true → q' info = true) :
    ∀ i, siteB q i = true → siteB q' i = true := by
  intro i hi
  unfold siteB at hi ⊢
  cases i with
  | call info =>
    have h2 : q info = true := hi
    exact hle info h2
  | tryCall info ti =>
    have h2 : q info = true := hi
    exact hle info h2
  | _ => exact hi

theorem allInsts_mono {vc : VCode} {p q : MInst → Bool}
    (hle : ∀ i, p i = true → q i = true) (h : allInsts vc p = true) :
    allInsts vc q = true := by
  unfold allInsts at h ⊢
  rw [Array.all_eq_true_iff_forall_mem] at h ⊢
  intro vb hb
  have hv := Array.all_eq_true_iff_forall_mem.mp (h vb hb)
  exact Array.all_eq_true_iff_forall_mem.mpr fun i hi => hle i (hv i hi)

theorem allInsts_siteOk_le {vc : VCode} {P : Clif.Program} {g : Clif.Function}
    {may : Clif.Function → Bool} (h : allInsts vc (siteB (siteOk P g may vc)) = true) :
    allInsts vc (siteB (siteOkTC P g may vc)) = true := by
  refine allInsts_mono (fun i hi => siteB_mono (fun _ => siteOk_le_siteOkTC) i hi) h

theorem siteOkTC_eq_siteOk {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} {n : String} (hd : info.dest = .sym n) :
    siteOkTC P g may vc info = siteOk P g may vc info := by
  unfold siteOkTC
  rw [hd]
  simp [Bool.or_false]

/-- **`siteOk_sound` for the widened check** at a `.sym` destination: `siteOk`'s conclusion. -/
theorem siteOkTC_sound {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : siteOkTC P g may vc info = true) {n : String}
    {h' : Clif.Function} (hd : info.dest = .sym n) (hf : P.func? n = some h') :
    (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      (Ld.map (·.1)).take (sigRets h'.sig).length =
        (List.range (min (sigRets h'.sig).length Ld.length)).map Reg.x :=
  siteOk_sound (siteOkTC_eq_siteOk hd ▸ h) hd hf

theorem siteOkTC_eq_blrOkTC {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} {r : Reg} (hd : info.dest = .reg r) :
    siteOkTC P g may vc info = blrOkTC P may (gotOf vc) info := by
  simp [siteOkTC, blrOkTC, siteOk, hd]

/-- **The `blr` fact of the widened check**: at a `.reg` destination, `blrOkTC` holds. -/
theorem siteOkTC_reg {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : allInsts vc (siteB (siteOkTC P g may vc)) = true)
    (hs : vc.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n) :
    blrOkTC P may (gotOf vc) info = true := by
  have h1 := site_sound h hs
  cases hd : info.dest with
  | sym n => exact absurd hd (hreg n)
  | reg r => rw [siteOkTC_eq_blrOkTC hd] at h1; exact h1

/-! ## The widened per-function link checks -/

/-- **`linkChks` with the widened call-site check** (`linkChksT`): as `linkChks`, with
`siteOkTC` in the `callRegs/blrRegs` entry. -/
def linkChksT (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let may := indToB (fun n => I.syms.lookup n) g
  [("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !calleeB P (fun n => I.syms.lookup n) g || ((!g.slots.isEmpty || fr.size == a.af.frameSize) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOkTC P g may a.vcp))),
   ("declSig", g.externs.all fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
   ("raCall/raBlr", raCallB T g a),
   ("indScope/indSig", indB P (fun n => I.syms.lookup n) g)]

/-- `siteOk` with the program's functions looked up through `F`, widened. -/
def siteWithOkTC (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (vc : VCode) (info : CallInfo) : Bool :=
  siteWithOk F P g may vc info ||
    match info.dest with
    | .reg (.vreg t .int) =>
      P.funcs.all fun h => !may h ||
        (match gotOf vc t with | some n => h.name != n | none => false)
    | _ => false

theorem siteWithOkTC_func? (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool)
    (vc : VCode) : siteWithOkTC P.func? P g may vc = siteOkTC P g may vc := rfl

/-- **`linkChksWith` with the widened call-site check** (`linkChksWithT`). -/
def linkChksWithT (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkTC C.F P g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallFastB C.ents g a),
   ("indScope/indSig", indFastB P C.S g)]

theorem linkChksWithT_of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) :
    linkChksWithT (LinkCtx.of I P T) P g r = linkChksT I P T g r := by
  simp only [linkChksWithT, linkChksT, LinkCtx.of, assocMap_fun, funcMap_fun, indToWithB_declSet,
    indFastB_eq, calleeSet_contains, raCallFastB_eq, siteWithOkTC_func?]
  rfl

end E2E.LinkCheck
