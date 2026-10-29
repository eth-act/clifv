module

public import FV.Backend.Proof.SpillCtlPipe
public import FV.Backend.Proof.SpillCtlFormsT
public import FV.Backend.Proof.AbiClass
public import FV.Backend.Proof.DriverCheckTy

@[expose] public section

/-!
# The registers of the typed AAPCS64 placement (S11e5 Stage C, slice 5)

`sigArgLocs` (`FV/Backend/Isel.lean`) places integer parameters in x0..x7, `f32`/`f64` ones in
v0..v7 (separate counters), an `sret` parameter in x8, the rest on the stack. For a signature
with at most one `sret` parameter (`AbiSigsOk`), `sigArgLocs_regsC`: the registers it uses are
pairwise distinct, and each parameter's location is x8 (an `sret` parameter) or a register of
its class (`RetRegC (tyClass p.ty)`: x0..x7 for an integer, v0..v7 for a float). The integer
`locsOf_regs` (`SpillCtlPipe`) is the case of integer parameters.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-- Two lists related position by position (same length). -/
inductive Pw2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw2 R [] []
  | cons {a : α} {b : β} {l1 : List α} {l2 : List β} : R a b → Pw2 R l1 l2 → Pw2 R (a :: l1) (b :: l2)

theorem Pw2.append {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l3 : List α} {l2 l4 : List β}, Pw2 R l1 l2 → Pw2 R l3 l4 → Pw2 R (l1 ++ l3) (l2 ++ l4)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h1 h2, h => .cons h1 (Pw2.append h2 h)

/-- The related pairs at one index. -/
theorem Pw2.get {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Pw2 R l1 l2 → ∀ {i : Nat} {b : β}, l2[i]? = some b →
      ∃ a, l1[i]? = some a ∧ R a b
  | _ :: _, _ :: _, .cons h1 _, 0, _, hb => by simp at hb; subst hb; exact ⟨_, rfl, h1⟩
  | _ :: _, _ :: _, .cons _ h2, i + 1, _, hb => by simpa using Pw2.get h2 (by simpa using hb)
  | [], [], .nil, _, _, hb => by simp at hb

/-- A location of a value of class `c`: a register of that class among x0..x7 / v0..v7, or a
stack slot. -/
def LocCls (c : RegClass) (l : ArgLoc) : Prop := ∀ r, l = .reg r → RetRegC c r

/-- The location of a parameter: x8 for an `sret` parameter, else of its class. -/
def PLoc (p : Clif.AbiParam) (l : ArgLoc) : Prop :=
  (p.purpose = .sret ∧ l = .reg (.x 8)) ∨ (p.purpose ≠ .sret ∧ LocCls (tyClass p.ty) l)

/-- The invariant of `argLocsC`'s fold: the registers used so far are distinct, below the
counters. -/
def RegsInv (acc : Array ArgLoc) (nx nv : Nat) : Prop :=
  nx ≤ 8 ∧ nv ≤ 8 ∧ (locRegs acc.toList).Nodup ∧
    ∀ r ∈ locRegs acc.toList, (∃ k, k < nx ∧ r = .x k) ∨ (∃ k, k < nv ∧ r = .v k)

theorem locRegs_push_reg (acc : Array ArgLoc) (r : Reg) :
    locRegs (acc.push (.reg r)).toList = locRegs acc.toList ++ [r] := by
  rw [Array.toList_push, locRegs_append]; rfl

theorem locRegs_push_stack (acc : Array ArgLoc) (o : Nat) :
    locRegs (acc.push (.stack o)).toList = locRegs acc.toList := by
  rw [Array.toList_push, locRegs_append]; simp [locRegs]

theorem argLocStep_inv : ∀ (ps : List (RegClass × Nat)) (acc : Array ArgLoc) (nx nv st : Nat)
    (cs : List RegClass), RegsInv acc nx nv → Pw2 LocCls cs acc.toList →
    RegsInv (ps.foldl argLocStep (acc, nx, nv, st)).1 (ps.foldl argLocStep (acc, nx, nv, st)).2.1
        (ps.foldl argLocStep (acc, nx, nv, st)).2.2.1 ∧
      Pw2 LocCls (cs ++ ps.map (·.1)) (ps.foldl argLocStep (acc, nx, nv, st)).1.toList
  | [], acc, nx, nv, st, cs, hI, hF => by simpa using ⟨hI, hF⟩
  | (c, b) :: ps, acc, nx, nv, st, cs, hI, hF => by
    obtain ⟨hx, hv, hnd, hin⟩ := hI
    rw [List.foldl_cons, List.map_cons, show cs ++ c :: ps.map (·.1) = (cs ++ [c]) ++ ps.map (·.1) by simp]
    cases c with
    | int =>
      by_cases h : nx < 8
      · have e : argLocStep (acc, nx, nv, st) (.int, b) = (acc.push (.reg (.x nx)), nx + 1, nv, st) := by
          simp [argLocStep, h]
        rw [e]
        refine argLocStep_inv ps _ _ _ _ _ ⟨by omega, hv, ?_, ?_⟩ ?_
        · rw [locRegs_push_reg, List.nodup_append]
          refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb; subst hb
          rintro rfl
          rcases hin _ ha with ⟨k, hk, he⟩ | ⟨k, -, he⟩ <;> cases he; omega
        · intro r hr
          rw [locRegs_push_reg, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · rcases hin r hr with ⟨k, hk, rfl⟩ | h2
            · exact .inl ⟨k, by omega, rfl⟩
            · exact .inr h2
          · exact .inl ⟨nx, by omega, rfl⟩
        · rw [Array.toList_push]
          exact Pw2.append hF (.cons (fun r e => by cases e; exact .inl ⟨rfl, nx, h, rfl⟩) .nil)
      · have e : argLocStep (acc, nx, nv, st) (.int, b) =
            (acc.push (.stack (alignTo st (max b 8))), nx, nv, alignTo st (max b 8) + max b 8) := by
          simp [argLocStep, h]
        rw [e]
        refine argLocStep_inv ps _ _ _ _ _ ⟨hx, hv, ?_, ?_⟩ ?_
        · rw [locRegs_push_stack]; exact hnd
        · rw [locRegs_push_stack]; exact hin
        · rw [Array.toList_push]
          exact Pw2.append hF (.cons (fun r e => by cases e) .nil)
    | float =>
      by_cases h : nv < 8
      · have e : argLocStep (acc, nx, nv, st) (.float, b) = (acc.push (.reg (.v nv)), nx, nv + 1, st) := by
          simp [argLocStep, h]
        rw [e]
        refine argLocStep_inv ps _ _ _ _ _ ⟨hx, by omega, ?_, ?_⟩ ?_
        · rw [locRegs_push_reg, List.nodup_append]
          refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb; subst hb
          rintro rfl
          rcases hin _ ha with ⟨k, -, he⟩ | ⟨k, hk, he⟩ <;> cases he; omega
        · intro r hr
          rw [locRegs_push_reg, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · rcases hin r hr with h1 | ⟨k, hk, rfl⟩
            · exact .inl h1
            · exact .inr ⟨k, by omega, rfl⟩
          · exact .inr ⟨nv, by omega, rfl⟩
        · rw [Array.toList_push]
          exact Pw2.append hF (.cons (fun r e => by cases e; exact .inr ⟨rfl, nv, h, rfl⟩) .nil)
      · have e : argLocStep (acc, nx, nv, st) (.float, b) =
            (acc.push (.stack (alignTo st (max b 8))), nx, nv, alignTo st (max b 8) + max b 8) := by
          simp [argLocStep, h]
        rw [e]
        refine argLocStep_inv ps _ _ _ _ _ ⟨hx, hv, ?_, ?_⟩ ?_
        · rw [locRegs_push_stack]; exact hnd
        · rw [locRegs_push_stack]; exact hin
        · rw [Array.toList_push]
          exact Pw2.append hF (.cons (fun r e => by cases e) .nil)

/-- **`argLocsC`'s registers**: distinct, each of its value's class, none of them x8. -/
theorem argLocsC_regs (ps : List (RegClass × Nat)) :
    (locRegs (argLocsC ps).1).Nodup ∧ Reg.x 8 ∉ locRegs (argLocsC ps).1 ∧
      Pw2 LocCls (ps.map (·.1)) (argLocsC ps).1 := by
  have := argLocStep_inv ps #[] 0 0 0 [] ⟨by omega, by omega, by simp [locRegs], by simp [locRegs]⟩ .nil
  obtain ⟨⟨hx, -, hnd, hin⟩, hF⟩ := this
  refine ⟨hnd, fun h8 => ?_, by simpa [argLocsC] using hF⟩
  rcases hin _ h8 with ⟨k, hk, he⟩ | ⟨k, -, he⟩ <;> cases he
  omega

theorem sretFold_ploc : ∀ (ps : List Clif.AbiParam) (acc : Array ArgLoc) (rest : List ArgLoc)
    (done : List Clif.AbiParam),
    Pw2 LocCls ((ps.filter (!·.purpose == .sret)).map (tyClass ·.ty)) rest →
    Pw2 PLoc done acc.toList →
    Pw2 PLoc (done ++ ps) (ps.foldl sretLocStep (acc, rest)).1.toList
  | [], acc, rest, done, _, hD => by simpa using hD
  | p :: ps, acc, rest, done, hR, hD => by
    rw [List.foldl_cons, show done ++ p :: ps = (done ++ [p]) ++ ps by simp]
    by_cases hp : (p.purpose == .sret) = true
    · have e : sretLocStep (acc, rest) p = (acc.push (.reg (.x 8)), rest) := by simp [sretLocStep, hp]
      rw [e]
      refine sretFold_ploc ps _ _ _ (by simpa [List.filter_cons, hp] using hR) ?_
      rw [Array.toList_push]
      exact Pw2.append hD (.cons (.inl ⟨by simpa using hp, rfl⟩) .nil)
    · have hR' := hR
      simp only [List.filter_cons, hp, Bool.not_false, ite_true, List.map_cons] at hR'
      cases hR' with
      | cons hl hrest =>
        rename_i l rest'
        have e : sretLocStep (acc, l :: rest') p = (acc.push l, rest') := by simp [sretLocStep, hp]
        rw [e]
        refine sretFold_ploc ps _ _ _ hrest ?_
        rw [Array.toList_push]
        exact Pw2.append hD (.cons (.inr ⟨by simpa using hp, hl⟩) .nil)

theorem map_cls_filter_zip (ps : List Clif.AbiParam) (bytes : List Nat) (hl : bytes.length = ps.length) :
    (((ps.zip bytes).filter (!·.1.purpose == .sret)).map fun q => (tyClass q.1.ty, q.2)).map (·.1) =
      (ps.filter (!·.purpose == .sret)).map (tyClass ·.ty) := by
  induction ps generalizing bytes with
  | nil => simp
  | cons p ps ih =>
    cases bytes with
    | nil => simp at hl
    | cons b bytes =>
      simp only [List.zip_cons_cons, List.filter_cons]
      split <;> simp_all

theorem map_cls_zip (ps : List Clif.AbiParam) (bytes : List Nat) (hl : bytes.length = ps.length) :
    ((ps.zip bytes).map fun q => (tyClass q.1.ty, q.2)).map (·.1) = ps.map (tyClass ·.ty) := by
  induction ps generalizing bytes with
  | nil => simp
  | cons p ps ih =>
    cases bytes with
    | nil => simp at hl
    | cons b bytes => simp_all

theorem forall₂_ploc_of_nosret : ∀ {ps : List Clif.AbiParam} {ls : List ArgLoc},
    (∀ p ∈ ps, p.purpose ≠ .sret) → Pw2 LocCls (ps.map (tyClass ·.ty)) ls → Pw2 PLoc ps ls
  | [], [], _, _ => .nil
  | p :: ps, l :: ls, hn, .cons h1 h2 =>
    .cons (.inr ⟨hn p (by simp), h1⟩) (forall₂_ploc_of_nosret (fun q hq => hn q (by simp [hq])) h2)

/-- **The registers of the typed placement**: on a signature with at most one `sret` parameter,
`sigArgLocs`' registers are pairwise distinct and every parameter's location is x8 (`sret`) or of
its class. -/
theorem sigArgLocs_regsC {s : Clif.Signature} (h1 : (s.params.filter (·.purpose == .sret)).length ≤ 1)
    {locs : List ArgLoc} {n : Nat} (h : sigArgLocs s = .ok (locs, n)) :
    (locRegs locs).Nodup ∧ Pw2 PLoc s.params locs := by
  unfold sigArgLocs at h
  cases hb : sigArgs s with
  | error e => rw [hb] at h; cases h
  | ok bytes =>
    have hl := sigArgs_length hb
    simp only [hb, bind, Except.bind, paramLocs] at h
    split at h
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨hnd, h8, hF⟩ := argLocsC_regs (((s.params.zip bytes).filter
          (!·.1.purpose == .sret)).map fun q => (tyClass q.1.ty, q.2))
        rw [map_cls_filter_zip _ _ hl] at hF
        refine ⟨nodup_of_count_le_one fun r => ?_, by
          simpa using sretFold_ploc s.params #[] _ [] hF .nil⟩
        have hc := sretFold_count r s.params (#[], (argLocsC (((s.params.zip bytes).filter
          (!·.1.purpose == .sret)).map fun q => (tyClass q.1.ty, q.2))).1)
        have e0 : locRegs (#[] : Array ArgLoc).toList = [] := rfl
        rw [e0, List.count_nil] at hc
        by_cases hr : r = .x 8
        · subst hr
          have : (locRegs (argLocsC (((s.params.zip bytes).filter
              (!·.1.purpose == .sret)).map fun q => (tyClass q.1.ty, q.2))).1).count (.x 8) = 0 :=
            List.count_eq_zero.mpr h8
          simp only [if_true] at hc; simpa using (by omega : _ ≤ 1)
        · simp only [hr, if_false] at hc
          have := count_le_one_of_nodup hnd r
          simpa using (by omega : _ ≤ 1)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨hnd, -, hF⟩ := argLocsC_regs ((s.params.zip bytes).map fun q => (tyClass q.1.ty, q.2))
      rw [h] at hnd hF
      rw [map_cls_zip _ _ hl] at hF
      rename_i hns
      refine ⟨hnd, forall₂_ploc_of_nosret (fun p hp he => hns ?_) hF⟩
      exact List.any_eq_true.mpr ⟨p, hp, by simp [he]⟩

/-! ## The typed entry `Args` -/

/-- The `(vreg, class, register)` triples of the register-passed entry parameters (typed). -/
def entryDC (ctx : Ctx) (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)) :
    List (Nat × RegClass × Reg) :=
  E.filterMap fun q => match q.1.2 with
    | .reg p => some (q.1.1.1, valClassOf ctx q.1.1.1, p)
    | .stack _ => none

theorem entryRegsT_eqC (ctx : Ctx) (R : Reg → Reg) :
    ∀ (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)),
    (∀ q ∈ E, R (Driver.vregOf ctx q.1.1.1) = Driver.vregOf ctx q.1.1.1) →
    E.filterMap (Driver.entryRegOfT ctx R) = argPairsC (entryDC ctx E)
  | [], _ => rfl
  | q :: E, h => by
    have ih := entryRegsT_eqC ctx R E (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    obtain ⟨⟨⟨v, ty⟩, l⟩, b⟩ := q
    have hv := h _ List.mem_cons_self
    cases l with
    | reg p =>
      simp only [List.filterMap_cons, Driver.entryRegOfT, entryDC, argPairsC, List.map_cons] at ih hv ⊢
      rw [hv, ih]; rfl
    | stack o =>
      simp only [List.filterMap_cons, Driver.entryRegOfT, entryDC] at ih ⊢
      exact ih

theorem entryDC_sub (ctx : Ctx) : ∀ (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)),
    ((entryDC ctx E).map (·.2.2)).Sublist (locRegs (E.map (·.1.2))) ∧
      ((entryDC ctx E).map (·.1)).Sublist (E.map (·.1.1.1))
  | [] => by simp [entryDC, locRegs]
  | q :: E => by
    obtain ⟨h1, h2⟩ := entryDC_sub ctx E
    obtain ⟨⟨⟨v, ty⟩, l⟩, b⟩ := q
    cases l with
    | reg p =>
      simp only [entryDC, List.filterMap_cons, List.map_cons, locRegs] at h1 h2 ⊢
      exact ⟨h1.cons₂ _, h2.cons₂ _⟩
    | stack o =>
      simp only [entryDC, List.filterMap_cons, List.map_cons, locRegs] at h1 h2 ⊢
      exact ⟨h1, h2.cons _⟩

theorem mem_entryDC {ctx : Ctx} {f : Clif.Function} {B : Clif.Block} {q : Nat × RegClass × Reg}
    (h : q ∈ entryDC ctx (Driver.entryParams f B)) :
    ∃ (i : Nat) (x : Clif.ValueId) (t : Clif.Ty) (p : Reg), B.params[i]? = some (x, t) ∧
      (locsOf f.sig)[i]? = some (ArgLoc.reg p) ∧
      q = (x, valClassOf ctx x, p) := by
  simp only [entryDC, List.mem_filterMap] at h
  obtain ⟨⟨⟨⟨x, t⟩, l⟩, b⟩, he, hq⟩ := h
  cases l with
  | stack o => cases hq
  | reg p =>
    simp only [Option.some.injEq] at hq
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    simp only [Driver.entryParams, List.getElem?_zip_eq_some] at hi
    exact ⟨i, x, t, p, hi.1.1, hi.1.2, hq.symm⟩

/-- **The typed entry `Args`** meets `SpillInstOk`: on a signature with at most one `sret`
parameter (an `i64`), with the entry parameters' vregs distinct and fixed by the renaming, and
each parameter's vreg of the class of the signature's parameter at its position (the CLIF
verifier's typing of the entry block). -/
theorem spillInstOk_entryArgsT {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {B : Clif.Block}
    (hsig : (f.sig.params.filter (·.purpose == .sret)).length ≤ 1)
    (hsret : ∀ p ∈ f.sig.params, p.purpose = .sret → p.ty = .i64)
    (hpar : (B.params.map (·.1)).Nodup)
    (hR : ∀ x ∈ B.params.map (·.1), R (Driver.vregOf ctx x) = Driver.vregOf ctx x)
    (hcls : ∀ (i : Nat) (x : Clif.ValueId) (t : Clif.Ty) (sp : Clif.AbiParam),
      B.params[i]? = some (x, t) → f.sig.params[i]? = some sp →
      valClassOf ctx x = tyClass sp.ty) :
    SpillInstOk (.args (Driver.entryRegsT f ctx R B)) := by
  have he : Driver.entryRegsT f ctx R B = argPairsC (entryDC ctx (Driver.entryParams f B)) := by
    unfold Driver.entryRegsT
    refine entryRegsT_eqC ctx R _ (fun q hq => hR _ ?_)
    unfold Driver.entryParams at hq
    exact List.mem_map_of_mem (List.of_mem_zip (List.of_mem_zip hq).1).1
  rw [he]
  obtain ⟨s1, s2⟩ := entryDC_sub ctx (Driver.entryParams f B)
  obtain ⟨hE1, hE2⟩ : ((Driver.entryParams f B).map (·.1.2)).Sublist (locsOf f.sig) ∧
      ((Driver.entryParams f B).map (·.1.1.1)).Sublist (B.params.map (·.1)) := by
    unfold Driver.entryParams; exact params3_sub _ _ _
  cases hloc : sigArgLocs f.sig with
  | error e =>
    have h0 : locsOf f.sig = [] := by simp [locsOf, hloc]
    have : Driver.entryParams f B = [] := by simp [Driver.entryParams, h0]
    rw [this]
    exact spillInstOk_argsC (by simp [entryDC]) (by simp [entryDC]) (by simp [entryDC])
  | ok r =>
    obtain ⟨locs, n⟩ := r
    have hl : locsOf f.sig = locs := by simp [locsOf, hloc]
    obtain ⟨hnd, hP⟩ := sigArgLocs_regsC hsig hloc
    have r1 := s1.trans (hE1.filterMap _)
    rw [hl] at r1
    refine spillInstOk_argsC (fun q hq => ?_) (hnd.sublist r1) (hpar.sublist (s2.trans hE2))
    obtain ⟨i, x, t, p, hb, hlc, rfl⟩ := mem_entryDC hq
    rw [hl] at hlc
    obtain ⟨sp, hsp, hpl⟩ := hP.get hlc
    have hc := hcls i x t sp hb hsp
    simp only
    rw [hc]
    rcases hpl with ⟨hs, he8⟩ | ⟨-, hlc'⟩
    · cases he8
      rw [hsret sp (List.mem_of_getElem? hsp) hs]
      exact .inl ⟨rfl, 8, Nat.le_refl _, rfl⟩
    · exact retRegC_argRegC (hlc' p rfl)

end Backend.Proof.Spill
