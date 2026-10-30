import FV.E2E.LinkCheck
import FV.E2E.LinkCheckFast
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

/-- The vreg index and class of a virtual register (`0`/`.int` for real registers). -/
def regVN : Reg → Nat
  | .vreg n _ => n
  | _ => 0

def regVC : Reg → RegClass
  | .vreg _ c => c
  | _ => .int

theorem argPairsC_of_virtual {us : List (Reg × Reg)}
    (hv : (us.all fun u => u.1.isVirtual = true) = true) :
    argPairsC (us.map fun u => (regVN u.1, regVC u.1, u.2)) = us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨u1, u2⟩ := u
    have hv' := List.all_eq_true.mp hv
    have hv1 : u1.isVirtual = true := by simpa using hv' (u1, u2) (List.mem_cons_self ..)
    have hv2 : (us.all fun v => v.1.isVirtual = true) = true :=
      List.all_eq_true.mpr fun x hx => hv' x (List.mem_cons_of_mem _ hx)
    cases hu : u1 with
    | vreg n c =>
      simp only [argPairsC, List.map_cons]
      rw [show List.map (fun q => (Reg.vreg q.1 q.2.1, q.2.2))
            (us.map fun v => (regVN v.1, regVC v.1, v.2)) =
          argPairsC (us.map fun v => (regVN v.1, regVC v.1, v.2)) from rfl, ih hv2]
      simp [regVN, regVC]
    | _ => simp [Reg.isVirtual, hu] at hv1

theorem callDefsC_of_virtual {ds : List (Reg × Reg)}
    (hv : (ds.all fun d => d.2.isVirtual = true) = true) :
    callDefsC (ds.map fun d => (d.1, regVN d.2, regVC d.2)) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨d1, d2⟩ := d
    have hv' := List.all_eq_true.mp hv
    have hv1 : d2.isVirtual = true := by simpa using hv' (d1, d2) (List.mem_cons_self ..)
    have hv2 : (ds.all fun v => v.2.isVirtual = true) = true :=
      List.all_eq_true.mpr fun x hx => hv' x (List.mem_cons_of_mem _ hx)
    cases hd : d2 with
    | vreg n c =>
      simp only [callDefsC, List.map_cons]
      rw [show List.map (fun q => (q.1, Reg.vreg q.2.1 q.2.2))
            (ds.map fun v => (v.1, regVN v.2, regVC v.2)) =
          callDefsC (ds.map fun v => (v.1, regVN v.2, regVC v.2)) from rfl, ih hv2]
      simp [regVN, regVC]
    | _ => simp [Reg.isVirtual, hd] at hv1

/-- **`blrOk` with typed `try_call`s**: `blrOk`, or a `blr` through the GOT whose uses' and defs'
targets are virtual registers and which enters no function of `P` (`may` admits none with the
GOT symbol's name) — a typed `try_call`'s callee is external (`InSubsetTC.tryExterns`), so the
base's contract covers the site. -/
def blrOkTC (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  blrOk P may got info ||
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

/-- **Soundness of the widened `blr` check**: `blrOk`'s conclusion, or the `blr`'s uses and defs
are virtual-register shaped and it enters no function of `P`. -/
theorem blrOkTC_sound {P : Clif.Program} {may : Clif.Function → Bool} {got : Nat → Option String}
    {info : CallInfo} (h : blrOkTC P may got info = true) :
    (∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) →
        (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x) ∨
    (∃ t L D, info = ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) → False) := by
  unfold blrOkTC at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rcases blrOk_sound h with ⟨t, Lu, Ld, heq, hall⟩
    exact .inl ⟨t, Lu, Ld, heq, hall⟩
  · split at h
    · next t heq =>
      split at h
      · next hu =>
        split at h
        · next hd =>
          cases info with
          | mk d0 u0 df0 =>
            refine .inr ⟨t, u0.map fun u => (regVN u.1, regVC u.1, u.2),
              df0.map fun d => (d.1, regVN d.2, regVC d.2), ?_, fun hfc hmem hm hgot => ?_⟩
            · have heq' : d0 = CallDest.reg (Reg.vreg t RegClass.int) := heq
              rw [heq', argPairsC_of_virtual hu, callDefsC_of_virtual hd]
            · have h1 := List.all_eq_true.mp h hfc hmem
              simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
              cases hg : got t
              · rw [hg] at h1
                simp only [Bool.false_or, reduceCtorEq] at h1
                rcases h1 with h2 | h2
                · rw [h2] at hm; exact Bool.noConfusion hm
                · exact h2.elim
              · rw [hg] at h1
                simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
                rcases h1 with h2 | h2
                · rw [h2] at hm; exact Bool.noConfusion hm
                · exact absurd (hgot _ hg) h2
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- `siteOk` with the widened `blr` check. -/
def siteOkTC (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode)
    (info : CallInfo) : Bool :=
  siteOk P g may vc info ||
    match info.dest with
    | .reg (.vreg t .int) =>
      match info.uses.all fun u => u.1.isVirtual = true with
      | true =>
        match info.defs.all fun d => d.2.isVirtual = true with
        | true =>
          P.funcs.all fun h => !may h ||
            (match gotOf vc t with | some n => h.name != n | none => false)
        | false => false
      | false => false
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
  unfold siteOkTC blrOkTC siteOk
  rw [hd]

/-- **The `blr` fact of the widened check**: at a `.reg` destination, `blrOkTC` holds. -/
theorem siteOkTC_reg {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : siteOkTC P g may vc info = true)
    (hreg : ∀ n, info.dest ≠ .sym n) :
    blrOkTC P may (gotOf vc) info = true := by
  cases hd : info.dest with
  | sym n => exact absurd hd (hreg n)
  | reg r => rw [siteOkTC_eq_blrOkTC hd] at h; exact h

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
     !calleeB P (fun n => I.syms.lookup n) g || ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
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
      match info.uses.all fun u => u.1.isVirtual = true with
      | true =>
        match info.defs.all fun d => d.2.isVirtual = true with
        | true =>
          P.funcs.all fun h => !may h ||
            (match gotOf vc t with | some n => h.name != n | none => false)
        | false => false
      | false => false
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
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
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

/-! ## Class-aware program call sites (#742)

A call of a function `h` of `P` passes its arguments in `h`'s parameter registers (`regLocs`:
x0..x7 and v0..v7 by class) and takes its results from `h`'s ABI return registers by class
(`sigRetRegs`: x0.. and v0.., as Cranelift's `compute_arg_locs` on the returns), with the call's
uses and defs vregs of either class (`argPairsC`/`callDefsC`). -/

/-- **The ABI return registers of a signature, by class** (AAPCS64, Cranelift's
`compute_arg_locs` on the returns): integer returns in x0.., `f32`/`f64` ones in v0.. (separate
counters, `retRegsT`); an `sret` signature without returns returns its struct pointer in x0 (its
only ABI return, `sigRets`). -/
def sigRetRegs (s : Clif.Signature) : List Reg :=
  if (s.params.any (·.purpose == .sret)) && s.returns.isEmpty then [.x 0]
  else retRegsT (s.returns.map fun p => tyClass p.ty) 0 0

theorem sigRets_of_sret {s : Clif.Signature} (hs : s.params.any (·.purpose == .sret) = true) :
    sigRets s = if s.returns.isEmpty then
      [(s.params.find? (·.purpose == .sret)).get (List.find?_isSome.mpr (List.any_eq_true.mp hs))]
      else s.returns := by
  unfold sigRets
  have hi := List.find?_isSome.mpr (List.any_eq_true.mp hs)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hi
  simp only [hp, Option.get_some]

theorem sigRetRegs_length (s : Clif.Signature) : (sigRetRegs s).length = (sigRets s).length := by
  unfold sigRetRegs
  cases hs : s.params.any (·.purpose == .sret) with
  | false =>
    rw [sigRets_of_noSret hs]
    simp [retRegsT_length]
  | true =>
    rw [sigRets_of_sret hs]
    cases he : s.returns.isEmpty <;> simp [retRegsT_length]

/-- For integer returns the ABI return registers are x0, x1, …. -/
theorem sigRetRegs_int {s : Clif.Signature} (hint : ∀ p ∈ s.returns, p.ty.isInt = true) :
    sigRetRegs s = (List.range (sigRets s).length).map Reg.x := by
  have hrep : s.returns.map (fun p => tyClass p.ty) = List.replicate s.returns.length .int := by
    refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    have := hint p hp
    unfold tyClass
    rw [if_pos this]
  have hx : retRegsT (s.returns.map fun p => tyClass p.ty) 0 0 =
      (List.range s.returns.length).map Reg.x := by
    rw [hrep, retRegsT_int, List.range_eq_range']
  unfold sigRetRegs
  cases hs : s.params.any (·.purpose == .sret) with
  | false =>
    rw [sigRets_of_noSret hs]
    simpa using hx
  | true =>
    rw [sigRets_of_sret hs]
    cases he : s.returns.isEmpty
    · simpa using hx
    · simp

/-- The defs of a call of a function of signature `sig` take its ABI results from its return
registers (`sigRetRegs`; the defs past them are a `try_call`'s exception payload registers). -/
def defsOkC (sig : Clif.Signature) (ds : List (Reg × Reg)) : Bool :=
  decide ((ds.map (·.1)).take (sigRets sig).length = (sigRetRegs sig).take ds.length)

theorem retPairs_eq_argPairsC (Lu : List (Nat × Reg)) :
    retPairs Lu = argPairsC (Lu.map fun q => (q.1, RegClass.int, q.2)) := by
  simp [retPairs, argPairsC, List.map_map, Function.comp_def]

theorem callDefs_eq_callDefsC (Ld : List (Reg × Nat)) :
    callDefs Ld = callDefsC (Ld.map fun q => (q.1, q.2, RegClass.int)) := by
  simp [callDefs, callDefsC, List.map_map, Function.comp_def]

/-- **The integer call-site facts of a callee with integer returns are the class-aware ones**
(integer vregs, results from x0..: `sigRetRegs` is x0.. for integer returns). -/
theorem siteRegsC_of_int {sig : Clif.Signature} (hint : ∀ p ∈ sig.returns, p.ty.isInt = true)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs sig)
    (hLd : (Ld.map (·.1)).take (sigRets sig).length =
      (List.range (min (sigRets sig).length Ld.length)).map Reg.x) :
    (Lu.map fun q => (q.1, RegClass.int, q.2)).map (·.2.2) = regLocs sig ∧
    ((Ld.map fun q => (q.1, q.2, RegClass.int)).map (·.1)).take (sigRets sig).length =
      (sigRetRegs sig).take (Ld.map fun q => (q.1, q.2, RegClass.int)).length := by
  refine ⟨by simpa [List.map_map, Function.comp_def] using hLu, ?_⟩
  have e1 : (Ld.map fun q => (q.1, q.2, RegClass.int)).map (·.1) = Ld.map (·.1) := by
    simp [List.map_map, Function.comp_def]
  rw [e1, hLd, sigRetRegs_int hint, List.length_map, ← List.map_take, List.take_range,
    Nat.min_comm]

/-- `siteOkTC`'s conclusion at a `.sym` site, for a callee with integer returns, in the
class-aware form of `LinkSys.OkT.callRegs`. -/
theorem callRegsC_of_int {sig : Clif.Signature} (hint : ∀ p ∈ sig.returns, p.ty.isInt = true)
    {info : CallInfo}
    (h : ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs sig ∧
      (Ld.map (·.1)).take (sigRets sig).length =
        (List.range (min (sigRets sig).length Ld.length)).map Reg.x) :
    ∃ n Lc Dc, info = ⟨.sym n, argPairsC Lc, callDefsC Dc⟩ ∧ Lc.map (·.2.2) = regLocs sig ∧
      (Dc.map (·.1)).take (sigRets sig).length = (sigRetRegs sig).take Dc.length := by
  obtain ⟨n, Lu, Ld, rfl, h1, h2⟩ := h
  exact ⟨n, _, _, by rw [retPairs_eq_argPairsC, callDefs_eq_callDefsC], siteRegsC_of_int hint h1 h2⟩

/-- **A class-aware `blr` site**: uses and defs on vregs (of either class), arguments in the
parameter registers of every function of `P` it may enter (`may`, and at a call through the GOT,
`got`, the GOT symbol's) with as many register parameters, and the results from that function's
return registers (`defsOkC`). -/
def blrOkC (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .reg (.vreg t .int) =>
    (info.uses.all fun u => u.1.isVirtual = true) && (info.defs.all fun d => d.2.isVirtual = true) &&
    P.funcs.all fun h => !may h ||
      (match got t with | some n => h.name != n | none => false) ||
      decide ((regLocs h.sig).length ≠ info.uses.length) ||
      (decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs)
  | _ => false

theorem blrOkC_sound {P : Clif.Program} {may : Clif.Function → Bool} {got : Nat → Option String}
    {info : CallInfo} (h : blrOkC P may got info = true) :
    ∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) →
        (regLocs h.sig).length = Lc.length →
        Lc.map (·.2.2) = regLocs h.sig ∧
        (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length := by
  obtain ⟨d, us, ds⟩ := info
  unfold blrOkC at h
  split at h
  · rename_i t hd
    simp only at hd
    subst hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hu, hdv⟩, hall⟩ := h
    refine ⟨t, us.map fun u => (regVN u.1, regVC u.1, u.2), ds.map fun d => (d.1, regVN d.2, regVC d.2),
      by rw [argPairsC_of_virtual hu, callDefsC_of_virtual hdv], fun h' hh hmay hgot hl => ?_⟩
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      Bool.and_eq_true] at hall
    simp only [List.map_map, Function.comp_def, List.length_map] at hl ⊢
    rcases hall h' hh with ((h1 | h1) | h1) | ⟨h1, h2⟩
    · rw [hmay] at h1; cases h1
    · revert h1
      cases hg : got t with
      | none => simp
      | some n => simp [hgot n hg]
    · exact absurd hl h1
    · exact ⟨h1, by simpa [defsOkC] using h2⟩
  · cases h

/-- **A class-aware call site**: a `bl` of a function `h` of `P` that `g` declares, uses and defs
on vregs (of either class), arguments in `h`'s parameter registers and the results from its
return registers (`defsOkC`); a `bl` of an extern outside `P` (the base's contract); or a `blr`
site (`blrOkC`, with the GOT symbols of `vc`). -/
def siteOkC (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        (info.uses.all fun u => u.1.isVirtual = true) &&
        (info.defs.all fun d => d.2.isVirtual = true) &&
        decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs
    | none => true
  | .reg _ => blrOkC P may (gotOf vc) info

theorem siteOkC_sound {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : siteOkC P g may vc info = true) {n : String}
    {h' : Clif.Function} (hd : info.dest = .sym n) (hf : P.func? n = some h') :
    (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lc Dc,
      info = ⟨.sym n, argPairsC Lc, callDefsC Dc⟩ ∧ Lc.map (·.2.2) = regLocs h'.sig ∧
      (Dc.map (·.1)).take (sigRets h'.sig).length = (sigRetRegs h'.sig).take Dc.length := by
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  unfold siteOkC at h
  simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hd, hu⟩, hdv⟩, h1⟩, h2⟩ := h
  refine ⟨hd, us.map fun u => (regVN u.1, regVC u.1, u.2), ds.map fun d => (d.1, regVN d.2, regVC d.2),
    by rw [argPairsC_of_virtual hu, callDefsC_of_virtual hdv], ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using h1
  · simpa [defsOkC, List.map_map, Function.comp_def] using h2

/-- **The `blr` fact of the class-aware check**: at a `.reg` destination, `blrOkC` holds. -/
theorem siteOkC_reg {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool}
    {vc : VCode} {info : CallInfo} (h : siteOkC P g may vc info = true)
    (hreg : ∀ n, info.dest ≠ .sym n) :
    blrOkC P may (gotOf vc) info = true := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOkC at h
  cases d with
  | reg r => exact h
  | sym n => exact absurd rfl (hreg n)

/-- `siteOkC` with the program's functions looked up through `F`. -/
def siteWithOkC (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (vc : VCode) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        (info.uses.all fun u => u.1.isVirtual = true) &&
        (info.defs.all fun d => d.2.isVirtual = true) &&
        decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs
    | none => true
  | .reg _ => blrOkC P may (gotOf vc) info

theorem siteWithOkC_func? (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool)
    (vc : VCode) : siteWithOkC P.func? P g may vc = siteOkC P g may vc := rfl

/-- **`indB` for the class-aware link contract**: the functions of `P` that `g` may enter through
an address with a signature one of its indirect calls matches take at most 8 register
parameters (the returns' check `indRetsB` of `indB` is not needed: an indirect call enters a
function only under `IndSigMatch`, which gives as many ABI returns). -/
def indBC (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  indFreeB g || P.funcs.all (fun h => !mayB S g h.name || !indSigB g h ||
      (match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false))

/-- `indBC P S g` with `indFreeB g`, `declB g`, `indSigs g` given. -/
def indWithBC (P : Clif.Program) (S : String → Option Nat) (ind : Bool) (D : String → Bool)
    (sigs : List Clif.Signature) : Bool :=
  ind || P.funcs.all (fun h => !mayWithB S ind D h.name || !indSigWithB D sigs h ||
      (match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false))

/-- **`indBC P S g` with `g`'s facts computed once** (`indFastBC_eq`). -/
def indFastBC (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  let D := declSet g
  indWithBC P S (indFreeB g) (fun n => D.contains n) (indSigs g)

theorem indFastBC_eq (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    indFastBC P S g = indBC P S g := by
  simp only [indFastBC, declSet_contains]
  rfl

/-- **The class-aware per-function link checks** (`linkChksTS`, #742): `linkChksT` with the
class-aware call-site check `siteOkC` and `indBC`. -/
def linkChksTS (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let may := indToB (fun n => I.syms.lookup n) g
  [("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !calleeB P (fun n => I.syms.lookup n) g || ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOkC P g may a.vcp))),
   ("declSig", g.externs.all fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
   ("raCall/raBlr", raCallB T g a),
   ("indScope/indSig", indBC P (fun n => I.syms.lookup n) g)]

/-- **`linkChksWith` with the class-aware checks** (`linkChksWithTS`). -/
def linkChksWithTS (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkC C.F P g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallFastB C.ents g a),
   ("indScope/indSig", indFastBC P C.S g)]

theorem linkChksWithTS_of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) :
    linkChksWithTS (LinkCtx.of I P T) P g r = linkChksTS I P T g r := by
  simp only [linkChksWithTS, linkChksTS, LinkCtx.of, assocMap_fun, funcMap_fun, indToWithB_declSet,
    indFastBC_eq, calleeSet_contains, raCallFastB_eq, siteWithOkC_func?]
  rfl

end E2E.LinkCheck
