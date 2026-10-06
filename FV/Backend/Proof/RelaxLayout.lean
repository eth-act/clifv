import FV.Backend.Proof.EncodeLayout

/-!
# M6: branch relaxation makes layout total

Notation: `L = fa.lines.toList` for `emitFunc k af = .ok fa`, `off j = lineOffset L j`.

* `relaxOf_fixpoint`: after relaxation with `relaxOf`, no relaxable branch is out of reach
  (`farTargets` is empty), and so (`farTargets_reaches`) every relaxable branch left reaches
  its label.
* `Insn.encodable`: an instruction's non-label operands encode (checked at a dummy PC where
  every label is at 0); `Insn.encode_of_encodable`: an encodable instruction encodes at any
  PC where its label operand is defined, in reach and aligned.
* `emitFunc_size`, `emitFunc_traps`: `emitFunc`'s size and trap table are what `FnAsm.layout`
  checks them against.
* `emitFunc_layout_total`: **layout cannot fail on branch range.** Given that the labels are
  defined once (`hlab`), every label operand names a defined label (`hdef`), every instruction's
  non-label operands encode (`henc`), the PC-relative forms relaxation does not handle (`b`
  aside) reach their labels (`NearOk`) and the function is under 128 MiB, `fa.layout`
  succeeds: relaxed branches are in reach by the fixpoint, `b` reaches ±128 MiB, the inverted
  short branch of a relaxed pair targets `pc + 8`, jump-table words fit 32 bits.
* `emitFunc_size_le`: relaxation at most doubles the code size.
-/

namespace Backend

open Arm

/-! ## Relaxation on line lists -/

private theorem relaxLines_cons' (f : Lbl → Bool) (ln : Line) (A : List Line) :
    relaxLines f (ln :: A) = relaxLine f ln ++ relaxLines f A := by
  simp [relaxLines]

theorem Insn.relaxTarget_invertTo_skip (c : Insn) : (c.invertTo .skip).relaxTarget? = none := by
  cases c <;> simp [Insn.invertTo, Insn.relaxTarget?, Insn.condTarget?]
  all_goals split <;> simp

/-- With every label far, no relaxable branch is left. -/
private theorem relaxable_relaxLines_true {pre : List Line} :
    ∀ ln ∈ relaxLines (fun _ => true) pre, ln.relaxable? = none := by
  intro ln hln
  simp only [relaxLines, List.mem_flatMap] at hln
  obtain ⟨ln0, _, hln⟩ := hln
  unfold relaxLine at hln
  split at hln
  · simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at hln
    rcases hln with rfl | rfl
    · simp [Line.relaxable?, Insn.relaxTarget_invertTo_skip]
    · simp [Line.relaxable?, Insn.relaxTarget?, Insn.condTarget?]
  · rename_i h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
    subst hln
    exact h

private theorem farTargets_go_of_none (m : Std.HashMap Lbl Nat) :
    ∀ {L : List Line} (pc : Nat) (acc : List Lbl), (∀ ln ∈ L, ln.relaxable? = none) →
      farTargets.go m L pc acc = acc
  | [], _, _, _ => rfl
  | ln :: L, pc, acc, h => by
    simp only [farTargets.go, h ln (by simp)]
    exact farTargets_go_of_none m _ _ fun x hx => h x (by simp [hx])

private theorem farTargets_of_none {L : List Line} (h : ∀ ln ∈ L, ln.relaxable? = none) :
    farTargets L = [] := by
  unfold farTargets
  split
  · exact farTargets_go_of_none _ _ _ h
  · rfl

private theorem relaxFar_fixpoint (pre : List Line) :
    ∀ n far, farTargets (relaxLines (relaxFar pre n far) pre) = []
  | 0, _ => farTargets_of_none relaxable_relaxLines_true
  | n + 1, far => by
    simp only [relaxFar]
    split
    · assumption
    · exact relaxFar_fixpoint pre n _

/-- **Fixpoint.** After relaxation no relaxable branch is out of reach of its label. -/
theorem relaxOf_fixpoint (pre : List Line) : farTargets (relaxLines (relaxOf pre) pre) = [] :=
  relaxFar_fixpoint pre _ _

private theorem farTargets_go_nil {m : Std.HashMap Lbl Nat} :
    ∀ {L : List Line} {pc : Nat} {acc : List Lbl}, farTargets.go m L pc acc = [] →
      acc = [] ∧ ∀ (j : Nat) (ln : Line) (c : Insn) (t : Lbl) (o : Nat), L[j]? = some ln →
        ln.relaxable? = some (c, t) → m[t]? = some o →
        c.reaches (pc + lineOffset L j) o = true
  | [], _, _, h => ⟨h, fun j ln _ _ _ hj => by simp at hj⟩
  | ln :: L, pc, acc, h => by
    simp only [farTargets.go] at h
    obtain ⟨h1, h2⟩ := farTargets_go_nil h
    refine ⟨?_, fun j ln' c t o hj hr ho => ?_⟩
    · split at h1
      · split at h1
        · split at h1
          · exact h1
          · simp at h1
        · exact h1
      · exact h1
    · cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [hr, ho] at h1
        cases hc : c.reaches pc o
        · simp [hc] at h1
        · simpa using hc
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [lineOffset_cons_succ, ← Nat.add_assoc]
        exact h2 j ln' c t o hj hr ho

/-- With no far targets, every relaxable branch reaches its label. -/
theorem farTargets_reaches {L : List Line} {m : Std.HashMap Lbl Nat} (h : farTargets L = [])
    (hm : labelOffsets.go L 0 {} = .ok m) {j : Nat} {ln : Line} {c : Insn} {t : Lbl} {o : Nat}
    (hj : L[j]? = some ln) (hr : ln.relaxable? = some (c, t)) (ho : m[t]? = some o) :
    c.reaches (lineOffset L j) o = true := by
  unfold farTargets at h
  rw [hm] at h
  simpa using (farTargets_go_nil h).2 j ln c t o hj hr ho

/-! ## Offset-independent encodability -/

/-- The non-label operands of `i` encode: `i` encodes at PC 0 with every label at 0. -/
def Insn.encodable (i : Insn) : Bool :=
  match i.encode ⟨0, fun _ => some 0⟩ with
  | .ok _ => true
  | .error _ => false

/-- The environment `Insn.encodable` checks against. -/
private abbrev env0 : Env := ⟨0, fun _ => some 0⟩

private theorem Insn.armFields_env_indep {i : Insn} (h : i.pcRelSpec? = none) (env env' : Env) :
    i.armFields env = i.armFields env' := by
  cases i <;> first | rfl | simp [Insn.pcRelSpec?] at h

private theorem Env.pcRel_of_range {env : Env} {what : String} {n scale : Nat} {l : Lbl}
    {o : Nat} {reach align : Int} (hl : env.target l = some o) (hs : 0 < scale)
    (hreach : (scale : Int) * 2 ^ n = reach) (halign : align = scale)
    (h1 : -reach ≤ (o : Int) - env.pc) (h2 : (o : Int) - env.pc < reach)
    (h3 : align ∣ (o : Int) - env.pc) :
    ∃ v, env.pcRel what (n + 1) scale l = .ok v := by
  subst hreach halign
  obtain ⟨q, hq⟩ := h3
  have hs' : (0 : Int) < scale := by omega
  have hq1 : -(2 ^ n : Int) ≤ q := by
    apply Int.le_of_mul_le_mul_left _ hs'
    rw [Int.mul_neg, ← hq]; exact h1
  have hq2 : q < 2 ^ n := by
    apply Int.lt_of_mul_lt_mul_left _ (Int.le_of_lt hs')
    rw [← hq]; exact h2
  have hdiv : ((o : Int) - env.pc) / scale = q := by
    rw [hq]; exact Int.mul_ediv_cancel_left _ (by omega)
  have hmod : ((o : Int) - env.pc) % scale = 0 := by
    rw [hq]; exact Int.mul_emod_right _ _
  unfold Env.pcRel Env.rel
  simp only [hl, Nat.add_sub_cancel, hmod, hdiv, hq1, hq2, and_self, ite_true, bne_self_eq_false,
    Bool.false_eq_true, ite_false, pure, bind, Except.bind, Except.pure]
  exact ⟨_, rfl⟩

/-- **Encodability.** An encodable instruction encodes at any PC where its label operand
(if any) is defined, within the form's reach and aligned. -/
theorem Insn.encode_of_encodable {i : Insn} {env : Env} (he : i.encodable = true)
    (hr : ∀ t reach align, i.pcRelSpec? = some (t, reach, align) → ∃ o, env.target t = some o ∧
      -reach ≤ (o : Int) - env.pc ∧ (o : Int) - env.pc < reach ∧ align ∣ (o : Int) - env.pc) :
    ∃ w, i.encode env = .ok w := by
  unfold Insn.encodable at he
  cases hs : i.pcRelSpec? with
  | none =>
    have : i.encode env = i.encode env0 := by
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields_env_indep hs env env0]
    rw [this]
    split at he
    · exact ⟨_, ‹_›⟩
    · simp at he
  | some p =>
    obtain ⟨t, reach, align⟩ := p
    obtain ⟨o, hl, h1, h2, h3⟩ := hr t reach align hs
    cases i <;> simp only [Insn.pcRelSpec?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
    all_goals obtain ⟨rfl, rfl, rfl⟩ := hs
    case b =>
      obtain ⟨v, hv⟩ := Env.pcRel_of_range (what := "b") (n := 25) hl (by decide) (by decide)
        rfl h1 h2 h3
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map]
      exact ⟨_, rfl⟩
    case bcond =>
      obtain ⟨v, hv⟩ := Env.pcRel_of_range (what := "b.cond") (n := 18) hl (by decide) (by decide)
        rfl h1 h2 h3
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map]
      exact ⟨_, rfl⟩
    case cbz nz w rt t =>
      obtain ⟨v, hv⟩ := Env.pcRel_of_range (what := "cbz") (n := 18) hl (by decide) (by decide)
        rfl h1 h2 h3
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map] at he ⊢
      cases hz : rt.encZR
      · cases hp : env0.pcRel "cbz" (18 + 1) 4 t <;> simp [hz, hp] at he
      · simp
    case tbz nz rt bit t =>
      obtain ⟨v, hv⟩ := Env.pcRel_of_range (what := "tbz") (n := 13) hl (by decide) (by decide)
        rfl h1 h2 h3
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map] at he ⊢
      by_cases hb : bit ≥ 64
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at he
      · cases hz : rt.encZR
        · cases hp : env0.pcRel "tbz" (13 + 1) 4 t <;> simp [hb, hz, hp] at he
        · simp [hb]
    case adr rd t =>
      obtain ⟨v, hv⟩ := Env.pcRel_of_range (what := "adr") (n := 20) hl (by decide) (by decide)
        rfl h1 h2 h3
      simp only [Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map] at he ⊢
      cases hz : rd.encZR
      · cases hp : env0.pcRel "adr" (20 + 1) 1 t <;> simp [hz, hp] at he
      · simp

/-- The unconditional branch of a relaxed pair is encodable. -/
theorem Insn.encodable_b (t : Lbl) : (Insn.b t).encodable = true := by
  cases t <;> rfl

/-- The inverted short branch of a relaxed pair is encodable when the original branch is. -/
theorem Insn.encodable_invertTo_skip {c : Insn} {t : Lbl} (hc : c.relaxTarget? = some t)
    (he : c.encodable = true) : (c.invertTo .skip).encodable = true := by
  cases c <;> simp [Insn.relaxTarget?, Insn.condTarget?] at hc
  case bcond x t' =>
    obtain ⟨v, hv⟩ := Env.pcRel_of_range (env := env0) (what := "b.cond") (n := 18) (scale := 4) (l := .skip)
      (o := 8) (reach := 2 ^ 20) rfl (by decide) (by decide) rfl (by decide) (by decide)
      (by decide)
    simp [Insn.invertTo, Insn.encodable, Insn.encode, Insn.toArmInst, Insn.armFields, hv, bind,
      Except.bind, pure, Except.pure, Functor.map, Except.map]
  case cbz nz w r t' =>
    obtain ⟨v, hv⟩ := Env.pcRel_of_range (env := env0) (what := "cbz") (n := 18) (scale := 4) (l := .skip)
      (o := 8) (reach := 2 ^ 20) rfl (by decide) (by decide) rfl (by decide) (by decide)
      (by decide)
    simp only [Insn.invertTo, Insn.encodable, Insn.encode, Insn.toArmInst, Insn.armFields, hv,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at he ⊢
    cases hz : r.encZR
    · cases hp : env0.pcRel "cbz" (18 + 1) 4 t' <;> simp [hz, hp] at he
    · simp
  case tbz nz r bit t' =>
    obtain ⟨v, hv⟩ := Env.pcRel_of_range (env := env0) (what := "tbz") (n := 13) (scale := 4) (l := .skip)
      (o := 8) (reach := 32 * 2 ^ 10) rfl (by decide) (by decide) rfl (by decide) (by decide)
      (by decide)
    simp only [Insn.invertTo, Insn.encodable, Insn.encode, Insn.toArmInst, Insn.armFields, hv,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at he ⊢
    by_cases hb : bit ≥ 64
    · simp [hb, throw, throwThe, MonadExceptOf.throw] at he
    · cases hz : r.encZR
      · cases hp : env0.pcRel "tbz" (13 + 1) 4 t' <;> simp [hb, hz, hp] at he
      · simp [hb]

/-! ## `emitFunc`'s size and trap table -/

/-- One step of `emitFunc`'s loop over the lines: running offset and trap sites. -/
private def trapStep (ln : Line) (s : Nat × Array TrapSite) : Nat × Array TrapSite :=
  match ln with
  | .ins _ (some code) => (s.1 + ln.size, s.2.push ⟨s.1, code⟩)
  | _ => (s.1 + ln.size, s.2)

/-- The trap sites of a line list laid out from byte offset `off`. -/
private def trapsFrom : List Line → Nat → List TrapSite
  | [], _ => []
  | ln :: L, off =>
    (match ln with
     | .ins _ (some c) => [⟨off, c⟩]
     | _ => []) ++ trapsFrom L (off + ln.size)

private theorem forIn_trapStep
    {f : Line → Nat × Array TrapSite → Except String (ForInStep (Nat × Array TrapSite))}
    (hf : ∀ ln s, f ln s = pure (.yield (trapStep ln s))) :
    ∀ (L : List Line) s, forIn L s f = pure (L.foldl (fun s ln => trapStep ln s) s)
  | [], _ => rfl
  | ln :: L, s => by
    simp only [List.forIn_cons, hf, pure_bind, List.foldl_cons]
    exact forIn_trapStep hf L _

private theorem foldl_trapStep : ∀ (L : List Line) (s : Nat × Array TrapSite),
    (L.foldl (fun s ln => trapStep ln s) s).1 = s.1 + (L.map Line.size).sum ∧
      (L.foldl (fun s ln => trapStep ln s) s).2.toList = s.2.toList ++ trapsFrom L s.1
  | [], s => by simp [trapsFrom]
  | ln :: L, s => by
    obtain ⟨h1, h2⟩ := foldl_trapStep L (trapStep ln s)
    simp only [List.foldl_cons, h1, h2, List.map_cons, List.sum_cons, trapsFrom]
    cases ln with
    | ins i t =>
      cases t <;> simp [trapStep, Nat.add_assoc]
    | word => simp [trapStep, Nat.add_assoc]
    | label => simp [trapStep, Nat.add_assoc]

private theorem emitFunc_unfold {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa) :
    ∃ pre, emitPre k af = .ok pre ∧
      fa.lines = (relaxLines (relaxOf pre.toList) pre.toList).toArray ∧
      fa.size = (fa.lines.toList.map Line.size).sum ∧ fa.traps = trapsFrom fa.lines.toList 0 := by
  unfold emitFunc at he
  cases hp : emitPre k af with
  | error e => simp [hp, bind, Except.bind] at he
  | ok pre =>
    simp only [hp, bind, Except.bind] at he
    rw [List.forIn_toArray, forIn_trapStep (fun ln s => by
      cases ln with
      | ins i t => cases t <;> rfl
      | word => rfl
      | label => rfl)] at he
    obtain ⟨h1, h2⟩ := foldl_trapStep (relaxLines (relaxOf pre.toList) pre.toList) (0, #[])
    simp only [pure, Except.pure, Except.ok.injEq] at he
    subst he
    exact ⟨pre, rfl, rfl, by simpa using h1, by simpa using h2⟩

private theorem sizes_codeLines : ∀ L : List Line, (L.map Line.size).sum = 4 * (codeLines L).length
  | [] => rfl
  | ln :: L => by
    have := sizes_codeLines L
    rw [codeLines_cons]
    cases h : ln.isLabel
    · simp [Line.size_of_not_isLabel h, this]; omega
    · simp [Line.size_of_isLabel h, this]

/-- `emitFunc`'s size is 4 bytes per code line (what `FnAsm.layout` checks). -/
theorem emitFunc_size {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa) :
    fa.size = 4 * (codeLines fa.lines.toList).length := by
  obtain ⟨_, _, _, hs, _⟩ := emitFunc_unfold he
  rw [hs, sizes_codeLines]

private theorem codeTraps_trapsFrom : ∀ (L : List Line) (n : Nat),
    ((codeLines L).zipIdx n).filterMap (fun (p : Line × Nat) => match p with
      | (ln, k) => match ln with
        | .ins _ (some c) => some (⟨4 * k, c⟩ : TrapSite)
        | _ => none) = trapsFrom L (4 * n)
  | [], _ => rfl
  | ln :: L, n => by
    rw [codeLines_cons]
    cases h : ln.isLabel
    · simp only [Bool.false_eq_true, ite_false, List.zipIdx_cons, List.filterMap_cons, trapsFrom]
      rw [codeTraps_trapsFrom L (n + 1), Line.size_of_not_isLabel h,
        show 4 * (n + 1) = 4 * n + 4 by omega]
      cases ln with
      | ins i t => cases t <;> rfl
      | word => rfl
      | label => simp [Line.isLabel] at h
    · simp only [ite_true, trapsFrom]
      rw [codeTraps_trapsFrom L n, Line.size_of_isLabel h, Nat.add_zero]
      cases ln with
      | ins => simp [Line.isLabel] at h
      | word => simp [Line.isLabel] at h
      | label => rfl

/-- `emitFunc`'s trap table is the trap sites of its code lines (what `FnAsm.layout` checks). -/
theorem emitFunc_traps {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa) :
    codeTraps (codeLines fa.lines.toList) = fa.traps := by
  obtain ⟨_, _, _, _, ht⟩ := emitFunc_unfold he
  rw [ht]
  exact codeTraps_trapsFrom _ 0

/-! ## Layout succeeds -/

/-- The labels a line's label operand names (other than `.skip`, which is `pc + 8`). -/
def Line.labelsUsed : Line → List Lbl
  | .ins i _ =>
    match i.pcRelSpec? with
    | some (t, _, _) => if t = .skip then [] else [t]
    | none => []
  | .word t b => [t, b]
  | .label _ => []

/-- The PC-relative lines relaxation does not handle (atomic-loop / jump-table-local labels,
`adr`, `b.al`/`b.nv`, branches with a trap code) reach their labels. -/
def NearOk (L : List Line) : Prop :=
  ∀ m, labelOffsets.go L 0 {} = .ok m →
    ∀ (j : Nat) (i : Insn) (tr : Option Clif.TrapCode) (t : Lbl) (reach align : Int) (o : Nat),
    L[j]? = some (.ins i tr) → i.pcRelSpec? = some (t, reach, align) → t ≠ .skip →
    (∀ x, i ≠ .b x) → (tr = none → i.relaxTarget? = none) → m[t]? = some o →
    -reach ≤ (o : Int) - lineOffset L j ∧ (o : Int) - lineOffset L j < reach

private theorem lineOffset_le_sum (L : List Line) (j : Nat) :
    lineOffset L j ≤ (L.map Line.size).sum := by
  have := congrArg (fun l => (l.map Line.size).sum) (List.take_append_drop j L)
  simp only [List.map_append, List.sum_append] at this
  unfold lineOffset
  omega

private theorem lineOffset_mod4 : ∀ (L : List Line) (j : Nat), lineOffset L j % 4 = 0
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | ln :: L, j + 1 => by
    rw [lineOffset_cons_succ]
    have := lineOffset_mod4 L j
    cases ln <;> simp [Line.size] <;> omega

private theorem Insn.pcRelSpec_bounds {i : Insn} {t : Lbl} {reach align : Int}
    (h : i.pcRelSpec? = some (t, reach, align)) :
    32768 ≤ reach ∧ reach ≤ 134217728 ∧ (align = 4 ∨ align = 1) := by
  cases i <;> simp only [Insn.pcRelSpec?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  all_goals decide

private theorem Insn.relaxTarget_pcRelSpec {i : Insn} {t t' : Lbl} {reach align : Int}
    (h : i.relaxTarget? = some t') (hs : i.pcRelSpec? = some (t, reach, align)) : t' = t := by
  have hc : i.condTarget? = some t' := by
    unfold Insn.relaxTarget? at h
    split at h <;> simp_all
  cases i <;> simp only [Insn.pcRelSpec?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  all_goals simp only [Insn.condTarget?, reduceCtorEq] at hc
  all_goals obtain ⟨rfl, -, -⟩ := hs
  case bcond => split at hc <;> simp_all
  all_goals simp_all

private theorem encodeCode_ne_error {lbl : Lbl → Option Nat} :
    ∀ {code : List Line} {acc : Array (BitVec 32)},
      (∀ (k : Nat) (ln : Line), code[k]? = some ln →
        ∃ w, ln.encodeAt lbl (4 * (acc.size + k)) = .ok w) →
      ∀ ctx e, encodeCode ctx lbl code acc ≠ .error e
  | [], _, _, _, _ => by simp [encodeCode, pure, Except.pure]
  | ln :: code, acc, h, ctx, e => by
    obtain ⟨w, hw⟩ := h 0 ln rfl
    simp only [encodeCode, Nat.add_zero] at hw ⊢
    rw [hw]
    refine encodeCode_ne_error (fun k ln' hk => ?_) ctx e
    obtain ⟨w', hw'⟩ := h (k + 1) ln' (by simpa using hk)
    exact ⟨w', by rw [Array.size_push, show acc.size + 1 + k = acc.size + (k + 1) by omega]; exact hw'⟩

/-- **Layout totality.** A function `emitFunc` produced lays out, given that its labels are
defined once and every label operand names a defined label, every instruction's non-label
operands encode, the PC-relative forms relaxation does not handle reach their labels
(`NearOk`), and the function is under 128 MiB: relaxation leaves no branch out of range. -/
theorem emitFunc_layout_total {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa)
    (hlab : ∃ m, labelOffsets fa.lines = .ok m)
    (hdef : ∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList)
    (henc : ∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true)
    (hnear : NearOk fa.lines.toList) (hsz : fa.size < 2 ^ 27) :
    ∃ fb, fa.layout = .ok fb := by
  obtain ⟨pre, _, hlines, hsize, _⟩ := emitFunc_unfold he
  obtain ⟨m, hm⟩ := hlab
  have hm' : labelOffsets.go fa.lines.toList 0 {} = .ok m := hm
  have hfar : farTargets fa.lines.toList = [] := by
    rw [hlines, List.toList_toArray]; exact relaxOf_fixpoint _
  have hsz' : fa.size < 134217728 := hsz
  -- every defined label is at an aligned offset within the function
  have hlbl : ∀ l, Line.label l ∈ fa.lines.toList →
      ∃ o, m[l]? = some o ∧ o ≤ fa.size ∧ o % 4 = 0 := by
    intro l hl
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hl
    exact ⟨_, labelOffsets_label hm hj, hsize ▸ lineOffset_le_sum _ _, lineOffset_mod4 _ _⟩
  -- every code line encodes at its offset
  have hline : ∀ (j : Nat) (ln : Line), fa.lines.toList[j]? = some ln → ln.isLabel = false →
      ∃ w, ln.encodeAt (m[·]?) (lineOffset fa.lines.toList j) = .ok w := by
    intro j ln hj hl
    have hmem : ln ∈ fa.lines.toList := List.mem_of_getElem? hj
    have hpc := hsize ▸ lineOffset_le_sum fa.lines.toList j
    have hpc4 := lineOffset_mod4 fa.lines.toList j
    cases ln with
    | label => simp [Line.isLabel] at hl
    | word t b =>
      obtain ⟨ot, hot, hot1, _⟩ := hlbl t (hdef _ hmem t (by simp [Line.labelsUsed]))
      obtain ⟨ob, hob, hob1, _⟩ := hlbl b (hdef _ hmem b (by simp [Line.labelsUsed]))
      simp only [Line.encodeAt, hot, hob]
      unfold sField
      split
      · exact ⟨_, rfl⟩
      · rename_i hn
        exact (hn (by simp only [show (2 : Int) ^ (32 - 1) = 2147483648 from rfl]; omega)).elim
    | ins i tr =>
      refine Insn.encode_of_encodable (henc i tr hmem) fun t reach align hs => ?_
      obtain ⟨hr1, hr2, hal⟩ := Insn.pcRelSpec_bounds hs
      by_cases hsk : t = .skip
      · subst hsk
        refine ⟨_, rfl, ?_, ?_, ?_⟩
        · push_cast; omega
        · push_cast; omega
        · rcases hal with rfl | rfl
          · exact ⟨2, by push_cast; omega⟩
          · exact ⟨8, by push_cast; omega⟩
      · have ht : t ∈ (Line.ins i tr).labelsUsed := by simp [Line.labelsUsed, hs, hsk]
        obtain ⟨o, ho, ho1, ho4⟩ := hlbl t (hdef _ hmem t ht)
        refine ⟨o, by rw [Env.target_of_ne hsk]; exact ho, ?_⟩
        simp only
        have hrange : -reach ≤ (o : Int) - lineOffset fa.lines.toList j ∧
            (o : Int) - lineOffset fa.lines.toList j < reach := by
          by_cases hb : ∃ x, i = .b x
          · obtain ⟨x, rfl⟩ := hb
            simp only [Insn.pcRelSpec?, Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨-, rfl, -⟩ := hs
            simp only [show (128 : Int) * 2 ^ 20 = 134217728 from rfl]
            omega
          · by_cases hrx : tr = none ∧ i.relaxTarget? ≠ none
            · obtain ⟨rfl, hrx⟩ := hrx
              obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hrx
              have := Insn.relaxTarget_pcRelSpec ht' hs
              subst this
              have hreach := farTargets_reaches hfar hm' hj
                (by simp [Line.relaxable?, ht'] : (Line.ins i none).relaxable? = some (i, t')) ho
              simp only [Insn.reaches, hs, decide_eq_true_eq] at hreach
              exact hreach
            · exact hnear m hm' j i tr t reach align o hj hs hsk (fun x h => hb ⟨x, h⟩)
                (fun htr => by
                  cases h : i.relaxTarget?
                  · rfl
                  · exact absurd ⟨htr, by simp [h]⟩ hrx) ho
        refine ⟨hrange.1, hrange.2, ?_⟩
        rcases hal with rfl | rfl
        · exact ⟨((o : Int) - lineOffset fa.lines.toList j) / 4, by omega⟩
        · exact Int.one_dvd _
  have hcode : ∀ (k' : Nat) (ln : Line), (codeLines fa.lines.toList)[k']? = some ln →
      ∃ w, ln.encodeAt (m[·]?) (4 * ((#[] : Array (BitVec 32)).size + k')) = .ok w := by
    intro k' ln hk
    obtain ⟨j, hj, hl, ho⟩ := line_of_codeLines hk
    rw [List.size_toArray, List.length_nil, Nat.zero_add, ← ho]
    exact hline j ln hj hl
  unfold FnAsm.layout
  simp only [hm, Except.mapError, bind, Except.bind]
  split
  · rename_i e heq
    exact absurd heq (encodeCode_ne_error hcode _ _)
  · rename_i ws heq
    have h1 : 4 * ws.size = fa.size := by
      rw [(encodeCode_spec heq).1, emitFunc_size he]; simp
    simp only [h1, emitFunc_traps he, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact ⟨_, rfl⟩

/-! ## Code size -/

private theorem relaxLine_size_le (f : Lbl → Bool) (ln : Line) :
    ((relaxLine f ln).map Line.size).sum ≤ 2 * ln.size := by
  unfold relaxLine
  split
  · rename_i c t h
    have : ln.size = 4 := by
      cases ln with
      | ins => rfl
      | word => rfl
      | label => simp [Line.relaxable?] at h
    split <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, this] <;> simp [Line.size]
  · simp; omega

theorem relaxLines_size_le (f : Lbl → Bool) :
    ∀ L : List Line, ((relaxLines f L).map Line.size).sum ≤ 2 * (L.map Line.size).sum
  | [] => by simp [relaxLines]
  | ln :: L => by
    rw [relaxLines_cons', List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have := relaxLines_size_le f L
    have := relaxLine_size_le f ln
    omega

/-- Relaxation at most doubles the code size. -/
theorem emitFunc_size_le {k : Nat} {af : AFunc} {fa : FnAsm} {pre : Array Line}
    (he : emitFunc k af = .ok fa) (hp : emitPre k af = .ok pre) :
    fa.size ≤ 2 * (pre.toList.map Line.size).sum := by
  obtain ⟨pre', hp', hlines, hsize, _⟩ := emitFunc_unfold he
  rw [hp] at hp'
  cases hp'
  rw [hsize, hlines, List.toList_toArray]
  exact relaxLines_size_le _ _

end Backend
