import FV.Concurrency.ArmAllocSeg
import FV.E2E.RegLevelMachine
import FV.Concurrency.VCodeAddrAtomic

/-!
# The events of the machine's steps through laid-out lines (T2h, #311, layer 4b)

The register-level proof runs the machine `ArmStepX X H fa` through the laid-out lines of an
item (`Backend.Proof.iterN_execLines`). The precise labels of the Arm thread are the events of
`stepi`'s decoded instruction (`ArmInstFoot.stepEvs`); at an unhooked instruction line they are
the events of the encoded instruction (`stepEvs_line`), so **the events of the machine's steps
through straight-line lines are the lines' events** (`segEvs_execLines`: `linesEvs`, step by
step). `flatten_nil`/`flatten_single`: a step-by-step list of at most one event.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread

/-- **The events of the machine's step at an unhooked instruction line** are the encoded
instruction's events. -/
theorem stepEvs_line {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {s : ArmState} {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64)
    (hj : fa.lines.toList[j]? = some (.ins i t)) (hi : i.hooked = false)
    (hprog : s.program = fb.program base)
    (hpc : r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (herr : r .ERR s = .None) :
    ∃ a, i.toArmInst ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = .ok a ∧
      ArmStepX X H fa s = exec_inst a s ∧ stepEvs s = instEvs a s ∧ decodeAt s = some a := by
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := X) (H := H) hl hm hfit hj hi hprog hpc herr
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hl hm hj rfl
  have hfetch : fetch_inst (r .PC s) s = some w := by
    rw [fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := base) (by have := (FnAsm.layout_size hl).1; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  have hd := Insn.decode_encode_of ha hw
  have hdec : decodeAt s = some a := by simp only [decodeAt, hfetch, hd]
  refine ⟨a, ha, hstep, ?_, hdec⟩
  unfold stepEvs
  rw [hdec]
  simp only [read_err, herr, ite_true]

/-- **The machine's steps through straight-line lines have the lines' events**, step by step
(the shape of `iterN_execLines`). -/
theorem segEvs_execLines {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) :
    ∀ (ls : List Line) (j : Nat) (s s' : ArmState),
      (∀ k ln, ls[k]? = some ln → fa.lines.toList[j + k]? = some ln) →
      (∀ i t, Line.ins i t ∈ ls → i.hooked = false) →
      s.program = fb.program base →
      r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) →
      r .ERR s = .None →
      InterOk ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s →
      execLines ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s = some s' →
      (segEvs (ArmStepX X H fa) ls.length s).flatten =
        linesEvs ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s
  | [], _, _, _, _, _, _, _, _, _, _ => by simp [segEvs, linesEvs]
  | .label _ :: _, _, _, _, _, _, _, _, _, _, h => by simp [execLines] at h
  | .word _ _ :: _, _, _, _, _, _, _, _, _, _, h => by simp [execLines] at h
  | .data _ :: _, _, _, _, _, _, _, _, _, _, h => by simp [execLines] at h
  | .ins i t :: ls, j, s, s', hat, hhook, hprog, hpc, herr, hinter, h => by
    have hj : fa.lines.toList[j]? = some (.ins i t) := by simpa using hat 0 _ rfl
    obtain ⟨a, ha, hstep, hev, -⟩ := stepEvs_line (X := X) (H := H) hl hm hfit hj
      (hhook i t (by simp)) hprog hpc herr
    simp only [execLines, ha] at h
    split at h
    · rename_i hpc'
      have hoff := lineOffset_succ fa.lines.toList j _ hj
      simp only [Line.size] at hoff
      simp only [List.length_cons, segEvs, List.flatten_cons, linesEvs, ha, hpc', ite_true, hev,
        hstep]
      congr 1
      cases ls with
      | nil => simp [segEvs, linesEvs]
      | cons ln ls' =>
        have h1 := hinter 1 (by omega) (by simp) (Arm.exec_inst a s)
          (by simp [execLines, ha, hpc'])
        have := segEvs_execLines (X := X) (H := H) (base := base) hl hm hfit (ln :: ls') (j + 1) _ s' (by
            intro k ln' hk
            have := hat (k + 1) ln' (by simpa using hk)
            rwa [show j + (k + 1) = j + 1 + k by omega] at this)
          (fun i' t' hm' => hhook i' t' (List.mem_cons_of_mem _ hm'))
          (by rw [h1.2, hprog])
          (by
            rw [hpc', hpc, hoff, BitVec.add_assoc]
            congr 1
            apply BitVec.eq_of_toNat_eq
            simp)
          h1.1
          (fun k hk0 hk s1 hs1 => by
            have := hinter (k + 1) (by omega) (by simp at hk ⊢; omega) s1
              (by simp [execLines, ha, hpc']; simpa [hoff] using hs1)
            exact ⟨this.1, by rw [this.2, h1.2]⟩)
          (by simpa [hoff] using h)
        rw [this]
        simp [hoff]
    · cases h

/-! ## Each step of a straight-line run -/

theorem execLines_ins : ∀ {env : Env} {ls : List Line} {s s' : ArmState},
    execLines env ls s = some s' → ∀ ln ∈ ls, ∃ x t, ln = .ins x t
  | _, [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | env, .ins i t :: ls, s, s', h => by
    intro ln hln
    rcases List.mem_cons.mp hln with rfl | hln
    · exact ⟨i, t, rfl⟩
    · simp only [execLines] at h
      split at h
      · split at h
        · exact execLines_ins h ln hln
        · cases h
      · cases h
  | _, .label _ :: _, _, _, h => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, h => by simp [execLines] at h
  | _, .data _ :: _, _, _, h => by simp [execLines] at h

theorem execLines_take {env : Env} {ls : List Line} {s s' : ArmState}
    (h : execLines env ls s = some s') (i : Nat) : ∃ s1, execLines env (ls.take i) s = some s1 := by
  rw [← List.take_append_drop i ls, VCodeAddr.execLines_append] at h
  cases h1 : execLines env (ls.take i) s with
  | none => rw [h1] at h; cases h
  | some s1 => exact ⟨s1, rfl⟩

theorem interOk_take {env : Env} {ls : List Line} {s : ArmState} (h : InterOk env ls s) (i : Nat) :
    InterOk env (ls.take i) s := by
  intro k hk0 hk s1 hs1
  simp only [List.length_take] at hk
  exact h k hk0 (by omega) s1 (by rwa [List.take_take, Nat.min_eq_left (by omega)] at hs1)

/-- **Each machine step of a straight-line run** executes the line's encoded instruction from an
error-free state; its events are that instruction's. -/
theorem step_execLines {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) {ls : List Line} {j : Nat} {s s' : ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = fb.program base)
    (hpc : r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (herr : r .ERR s = .None)
    (hinter : InterOk ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s)
    (hrun : execLines ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s = some s') :
    ∀ i < ls.length, ∃ x t a, ls[i]? = some (.ins x t) ∧
      x.toArmInst ⟨lineOffset fa.lines.toList (j + i), (lm[·]?)⟩ = .ok a ∧
      decodeAt (iterN (ArmStepX X H fa) i s) = some a ∧
      stepEvs (iterN (ArmStepX X H fa) i s) = instEvs a (iterN (ArmStepX X H fa) i s) ∧
      iterN (ArmStepX X H fa) (i + 1) s = exec_inst a (iterN (ArmStepX X H fa) i s) := by
  intro i hi
  obtain ⟨x, t, hx⟩ := execLines_ins hrun _ (List.getElem_mem hi)
  have hli : ls[i]? = some (.ins x t) := by rw [List.getElem?_eq_getElem hi, hx]
  obtain ⟨s1, h1⟩ := execLines_take hrun i
  have hit : iterN (ArmStepX X H fa) i s = s1 := by
    have := iterN_execLines (X := X) (H := H) hl hm hfit (ls.take i) j s s1
      (fun k ln hk => hat k ln (by
        rw [List.getElem?_take] at hk; split at hk
        · exact hk
        · cases hk))
      (fun i' t' hm' => hhook i' t' (List.mem_of_mem_take hm')) hprog hpc herr (interOk_take hinter i) h1
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  have hok : r .ERR s1 = .None ∧ s1.program = s.program := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      simp only [List.take_zero, execLines, Option.some.injEq] at h1
      subst h1
      exact ⟨herr, rfl⟩
    · exact hinter i h0 hi s1 h1
  have hpci := iterN_execLines_pc (X := X) (H := H) hl hm hfit ls j s s' hat hhook hprog hpc herr
    hinter hrun i (by omega)
  rw [hit] at hpci ⊢
  obtain ⟨a, ha, hstep, hev, hdec⟩ := stepEvs_line (X := X) (H := H) hl hm hfit
    (hat i _ hli) (hhook x t (by rw [← hx]; exact List.getElem_mem hi)) (by rw [hok.2, hprog]) hpci
    hok.1
  refine ⟨x, t, a, hli, ha, hdec, hev, ?_⟩
  rw [iterN_succ', hit, hstep]

/-- The class of an instruction without memory kind is `plain`. -/
theorem clsOf_none {env : Env} {i : Insn} {a : ArmInst} (h : i.toArmInst env = .ok a)
    (hk : Code.insnKind i = none) : clsOf a = .plain := by
  unfold Insn.toArmInst at h
  cases ha : i.armFields env with
  | error e => rw [ha] at h; cases h
  | ok a0 =>
    rw [ha] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have hm : VCodeEvents.memCls a0.norm = false := by
      rw [VCodeEvents.memCls_norm]; exact VCodeEvents.memCls_armFields env i a0 ha hk
    generalize a0.norm = b at hm
    cases b with
    | LDST _ => cases hm
    | BR i =>
      cases i with
      | Barrier _ => cases hm
      | _ => rfl
    | _ => rfl

/-- **A straight-line run without memory kinds**: every machine step has no event and is no
store exclusive. -/
theorem nomem_execLines {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) {ls : List Line} {j : Nat} {s s' : ArmState}
    (hk : Code.kinds ls = [])
    (hat : ∀ k ln, ls[k]? = some ln → fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (hprog : s.program = fb.program base)
    (hpc : r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (herr : r .ERR s = .None)
    (hinter : InterOk ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s)
    (hrun : execLines ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s = some s') :
    ∀ i < ls.length, stepEvs (iterN (ArmStepX X H fa) i s) = [] ∧
      NoStx (iterN (ArmStepX X H fa) i s) := by
  intro i hi
  obtain ⟨x, t, a, hli, ha, hdec, hev, -⟩ :=
    step_execLines (X := X) (H := H) hl hm hfit hat hhook hprog hpc herr hinter hrun i hi
  have hxk : Code.insnKind x = none := by
    have hmem := List.mem_of_getElem? hli
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hmem
    rw [hAB, Code.kinds_append, VCodeEvents.kinds_ins, List.append_eq_nil_iff, List.append_eq_nil_iff] at hk
    cases e : Code.insnKind x with
    | none => rfl
    | some k => rw [e] at hk; simp at hk
  refine ⟨by rw [hev]; exact VCodeEvents.instEvs_none ha hxk _, fun rel rs rn h => ?_⟩
  rw [cls_of_decode hdec, clsOf_none ha hxk] at h
  cases h

/-! ## Step-by-step lists of at most one event -/

theorem flatten_nil {α : Type} {L : List (List α)} (h : L.flatten = []) :
    ∀ i (hi : i < L.length), L[i] = [] := by
  intro i hi
  have := List.flatten_eq_nil_iff.mp h
  exact this _ (List.getElem_mem hi)

theorem flatten_single {α : Type} : ∀ {L : List (List α)} {x : α}, L.flatten = [x] →
    ∃ i0, ∃ hi : i0 < L.length, L[i0] = [x] ∧ ∀ i (h : i < L.length), i ≠ i0 → L[i] = []
  | [], _, h => by simp at h
  | l :: L, x, h => by
    simp only [List.flatten_cons] at h
    cases l with
    | nil =>
      simp only [List.nil_append] at h
      obtain ⟨i0, hi, h1, h2⟩ := flatten_single h
      refine ⟨i0 + 1, by simp; omega, by simpa using h1, fun i hi' hne => ?_⟩
      cases i with
      | zero => rfl
      | succ i => simpa using h2 i (by simp at hi'; omega) (by omega)
    | cons y l =>
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h
      obtain ⟨rfl, rfl, hL⟩ := h
      refine ⟨0, by simp, rfl, fun i hi' hne => ?_⟩
      cases i with
      | zero => exact absurd rfl hne
      | succ i => simpa using flatten_nil hL i (by simp at hi'; omega)

end Concurrency.ArmAllocThread
