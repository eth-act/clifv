module

public import FV.Concurrency.VCodeThread
public import FV.Concurrency.ProgramE2E

@[expose] public section

/-!
# Precise labels of Arm thread steps (T2h, #311)

`ArmThread.TStep` accepts every footprint of a step as its label, so a step may carry, besides its
access, a read and a write-back of any other location: a write to a shared location that no
compiler layer can account for. `ProgE2E.Realizes` cannot hold for such runs, so the Arm threads of
the final theorem are restricted to **precise labels** (`docs/plans/atomics.md` §3e, finding 1):

* `Precise s l`: the label of a step at `s` is the instruction's precise footprint
  (`ArmInstFoot.stepEvs`) on `s` with some memory (the bytes the environment provides), or a
  failing store exclusive; `ATStepP`: `ProgE2E.ATStep` with precise labels (`atStep_of_P`,
  `runs_of_P`: a restriction, so `ProgE2E.program_correct*` apply);
* `instEvs_setMem`/`stepEvs_setMem`: **the footprint on another memory is the same accesses with
  the read bytes taken from that memory** (`reread`);
* `exists_precise_step`: **the restriction is receptive**: for every memory `m` the
  environment may provide, a `stepi` thread step with the precise label `stepEvs (setMem m s)`
  exists (a store exclusive: when the policy lets it succeed), so precise runs read every value.
-/

namespace Concurrency.ArmPrecise

open Arm ArmFoot ArmThread ArmInstFoot Prog ProgE2E

/-! ## Footprints on another memory -/

/-- An event with its bytes read from `m` (a read), unchanged otherwise. -/
def reread1 (m : Memory) (e : Ev) : Ev :=
  if e.k.dir = .R then ⟨e.k, e.addr, e.n, readM e.n e.addr m⟩ else e

/-- The events with the read bytes taken from `m`. -/
def reread (m : Memory) (evs : List Ev) : List Ev := evs.map (reread1 m)

theorem reread_ite {c : Prop} [Decidable c] (m : Memory) (a b : List Ev) :
    reread m (if c then a else b) = if c then reread m a else reread m b := by
  split <;> rfl

theorem reread_nil (m : Memory) : reread m [] = [] := rfl

theorem reread_W {k : AKind} (hk : k.dir = .W) (m : Memory) (a : BitVec 64) (n : Nat)
    (v : BitVec (n * 8)) : reread m [⟨k, a, n, v⟩] = [⟨k, a, n, v⟩] := by
  simp only [reread, reread1, hk, List.map_cons, List.map_nil]; rfl

theorem reread_R {k : AKind} (hk : k.dir = .R) (m : Memory) (a : BitVec 64) (n : Nat)
    (v : BitVec (n * 8)) : reread m [⟨k, a, n, v⟩] = [⟨k, a, n, readM n a m⟩] := by
  simp only [reread, reread1, hk, ite_true, List.map_cons, List.map_nil]

theorem literal_address_sm (imm : BitVec 19) (m : Memory) (s : ArmState) :
    LDST.literal_address imm (setMem m s) = LDST.literal_address imm s := by
  simp only [LDST.literal_address, pc_sm]

macro "reread_tac" : tactic => `(tactic| (
  simp only [reread_ite]
  repeat' (first
    | rfl
    | (rw [reread_W (by rfl)])
    | (rw [reread_R (by rfl)])
    | (congr 1)
    | split)))

theorem immEvs_setMem (inst : LDST.Reg_imm_cls) (s : ArmState) (m : Memory) :
    immEvs inst (setMem m s) = reread m (immEvs inst s) := by
  unfold immEvs
  simp only [read_gpr_sm, check_sp_sm', ldst_read_sm, offset_value_sm, setMem_mem]
  reread_tac

theorem ldsturEvs_setMem (inst : Reg_unscaled_imm_cls) (s : ArmState) (m : Memory) :
    ldsturEvs inst (setMem m s) = reread m (ldsturEvs inst s) := by
  unfold ldsturEvs
  simp only [read_gpr_sm, check_sp_sm', read_sfp_sm, setMem_mem]
  reread_tac

theorem pairEvs_setMem (inst : LDST.Reg_pair_cls) (s : ArmState) (m : Memory) :
    pairEvs inst (setMem m s) = reread m (pairEvs inst s) := by
  unfold pairEvs
  simp only [read_gpr_sm, check_sp_sm', ldst_read_sm, setMem_mem, reread_ite, reread_nil]
  cases inst.L? <;>
    simp only [reread_W (k := AKind.plainW) rfl, reread_R (k := AKind.plainR) rfl]

theorem literalEvs_setMem (inst : Reg_literal_cls) (s : ArmState) (m : Memory) :
    literalEvs inst (setMem m s) = reread m (literalEvs inst s) := by
  unfold literalEvs litEv
  simp only [literal_address_sm, setMem_mem]
  reread_tac

theorem exclEvs_setMem (inst : Reg_exclusive_cls) (s : ArmState) (m : Memory) :
    exclEvs inst (setMem m s) = reread m (exclEvs inst s) := by
  unfold exclEvs
  simp only [read_gpr_sm, check_sp_sm', ldst_read_sm, setMem_mem]
  simp only [reread_ite, reread_nil]
  by_cases hL : inst.L = 1#1
  · simp only [hL, ite_true, reread_R (exclKind_R hL)]
  · simp only [hL, ite_false, reread_W (exclKind_W hL)]

/-- **An instruction's events on another memory are its accesses with that memory's bytes.** -/
theorem instEvs_setMem (ai : ArmInst) (s : ArmState) (m : Memory) :
    instEvs ai (setMem m s) = reread m (instEvs ai s) := by
  cases ai with
  | LDST i =>
    cases i with
    | Reg_unscaled_imm i =>
      simp only [instEvs, reread_ite, ldsturEvs_setMem, immEvs_setMem]
    | Reg_reg_offset i => simp only [instEvs, reread_ite, reread_nil, immEvs_setMem]
    | Reg_pair_pre_indexed i | Reg_pair_post_indexed i | Reg_pair_signed_offset i =>
      simp only [instEvs, pairEvs_setMem]
    | Reg_exclusive i => simp only [instEvs, exclEvs_setMem]
    | Reg_literal i => simp only [instEvs, literalEvs_setMem]
    | Reg_imm_post_indexed i | Reg_unsigned_imm i | Reg_imm_pre_indexed i =>
      simp only [instEvs, immEvs_setMem]
  | BR i =>
    cases i with
    | Barrier i => simp only [instEvs, reread_ite, reread_nil]; rfl
    | _ => rfl
  | _ => rfl

theorem errEvs_reread (ai : ArmInst) (m : Memory) : reread m (errEvs ai) = errEvs ai := by
  unfold errEvs
  split
  · simp only [reread_ite, reread_nil]; rfl
  · rfl

/-- **A step's events on another memory are its accesses with that memory's bytes.** -/
theorem stepEvs_setMem (s : ArmState) (m : Memory) :
    stepEvs (setMem m s) = reread m (stepEvs s) := by
  unfold stepEvs
  rw [decodeAt_setMem]
  split
  · rename_i ai _
    simp only [read_err, r_setMem, instEvs_setMem]
    by_cases hc : r StateField.ERR s = StateError.None
    · simp only [hc, ite_true]
    · simp only [hc, ite_false, errEvs_reread]
  · rfl

/-! ## Sizes -/

theorem shl8_le (k : Nat) (hk : k < 64) : (8 <<< k) / 8 ≤ 2 ^ 64 := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_div_cancel _ (by decide)]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- All events have at most `2 ^ 64` bytes. -/
def AllN (evs : List Ev) : Prop := ∀ e ∈ evs, e.n ≤ 2 ^ 64

theorem alln_nil : AllN [] := fun _ h => absurd h List.not_mem_nil

theorem alln_ite {c : Prop} [Decidable c] {a b : List Ev} (ha : c → AllN a) (hb : ¬ c → AllN b) :
    AllN (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

theorem alln_one {e : Ev} (h : e.n ≤ 2 ^ 64) : AllN [e] := by
  intro e' he'; simp only [List.mem_singleton] at he'; subst he'; exact h

theorem bv_lt64 {w : Nat} (b : BitVec w) (h : w ≤ 6) : b.toNat < 64 :=
  Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) h)

theorem n_immEvs (inst : LDST.Reg_imm_cls) (s : ArmState) : AllN (immEvs inst s) := by
  unfold immEvs
  dsimp only
  repeat' (first | exact alln_nil | (apply alln_ite <;> intro h))
  all_goals
    refine alln_one (shl8_le _ ?_)
    split
    · exact bv_lt64 _ (by decide)
    · exact bv_lt64 _ (by decide)

theorem n_ldsturEvs (inst : Reg_unscaled_imm_cls) (s : ArmState) : AllN (ldsturEvs inst s) := by
  unfold ldsturEvs
  dsimp only
  repeat' (first | exact alln_nil | (apply alln_ite <;> intro h))
  all_goals exact alln_one (shl8_le _ (bv_lt64 _ (by decide)))

theorem n_pairEvs (inst : LDST.Reg_pair_cls) (s : ArmState) : AllN (pairEvs inst s) := by
  have hp : ∀ k, k < 6 → 2 * ((8 <<< k) / 8) ≤ 2 ^ 64 := fun k hk => by
    rw [Nat.shiftLeft_eq, Nat.mul_comm 8, Nat.mul_div_cancel _ (by decide)]
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hs : (if (!inst.SIMD?) = true then 2 + (BitVec.lsb inst.opc 1).toNat
      else 2 + inst.opc.toNat) < 6 := by
    have h1 := (BitVec.lsb inst.opc 1).isLt
    have h2 := inst.opc.isLt
    split <;> simp only [Nat.reducePow] at h1 h2 <;> omega
  unfold pairEvs
  dsimp only
  repeat' (first | exact alln_nil | (apply alln_ite <;> intro h))
  cases inst.L? <;> exact alln_one (hp _ hs)

theorem n_exclEvs (inst : Reg_exclusive_cls) (s : ArmState) : AllN (exclEvs inst s) := by
  unfold exclEvs
  repeat' (first | exact alln_nil | (apply alln_ite <;> intro h))
  all_goals exact alln_one (shl8_le _ (bv_lt64 _ (by decide)))

theorem n_literalEvs (inst : Reg_literal_cls) (s : ArmState) : AllN (literalEvs inst s) := by
  unfold literalEvs litEv
  repeat' (first | exact alln_nil | (apply alln_ite <;> intro h))
  all_goals exact alln_one (by dsimp only; (try split) <;> decide)

/-- The events of an instruction are at most `2 ^ 64` bytes (at most 64). -/
theorem n_instEvs (ai : ArmInst) (s : ArmState) : AllN (instEvs ai s) := by
  cases ai with
  | LDST i =>
    cases i with
    | Reg_unscaled_imm i =>
      simp only [instEvs]
      exact alln_ite (fun _ => n_ldsturEvs _ s) (fun _ => n_immEvs _ s)
    | Reg_reg_offset i =>
      simp only [instEvs]
      exact alln_ite (fun _ => alln_nil) (fun _ => n_immEvs _ s)
    | Reg_pair_pre_indexed i | Reg_pair_post_indexed i | Reg_pair_signed_offset i =>
      exact n_pairEvs _ s
    | Reg_exclusive i => exact n_exclEvs _ s
    | Reg_literal i => exact n_literalEvs _ s
    | Reg_imm_post_indexed i | Reg_unsigned_imm i | Reg_imm_pre_indexed i => exact n_immEvs _ s
  | BR i =>
    cases i with
    | Barrier i =>
      simp only [instEvs]
      exact alln_ite (fun _ => alln_one (by decide)) (fun _ => alln_nil)
    | _ => exact alln_nil
  | _ => exact alln_nil

theorem len_stepEvs (s : ArmState) : (stepEvs s).length ≤ 1 := by
  unfold stepEvs
  split
  · split
    · exact VCodeThread.len_instEvs _ s
    · unfold errEvs; split
      · split <;> simp
      · simp
  · simp

theorem n_stepEvs (s : ArmState) : ∀ e ∈ stepEvs s, e.n ≤ 2 ^ 64 := by
  unfold stepEvs
  split
  · split
    · exact n_instEvs _ s
    · unfold errEvs; split
      · split
        · intro e he; simp only [List.mem_singleton] at he; subst he; decide
        · intro e he; exact absurd he List.not_mem_nil
      · intro e he; exact absurd he List.not_mem_nil
  · intro e he; exact absurd he List.not_mem_nil

/-- At most one event of at most `2 ^ 64` bytes agrees with the memory its reads are stored in. -/
theorem agrees_applyR {evs : List Ev} (hl : evs.length ≤ 1) (hn : ∀ e ∈ evs, e.n ≤ 2 ^ 64)
    (M : Memory) : Agrees evs (applyR evs M) := by
  match evs, hl with
  | [], _ => exact fun _ h => absurd h List.not_mem_nil
  | [e], _ =>
    intro e' he' hr
    simp only [List.mem_singleton] at he'; subst he'
    simp only [applyR, hr, ite_true]
    exact readM_writeM _ _ _ _ (hn _ List.mem_cons_self)

/-- A footprint at `setMem m s` is a footprint at `s`. -/
theorem footprint_of_setMem {f : ArmState → ArmState} {s : ArmState} {m : Memory} {evs : List Ev}
    (h : Footprint f (setMem m s) evs) (h1 : Agrees evs (applyR evs s.mem)) : Footprint f s evs := by
  intro m' hm'
  have e1 := h m' hm'
  have e2 := h (applyR evs s.mem) h1
  simp only [setMem_setMem, setMem_mem] at e1 e2
  rw [e1, e2, setMem_setMem]

theorem cls_setMem (s : ArmState) (m : Memory) : cls (setMem m s) = cls s := by
  unfold cls; rw [decodeAt_setMem]

/-! ## Precise labels -/

/-- **The label of a step at `s` is precise**: a failing store exclusive, or the instruction's
footprint `stepEvs` on `s` with some memory (the bytes the environment provides). -/
def Precise (s : ArmState) (l : Lab) : Prop :=
  l.xfail = true ∨ ∃ m, l.evs = stepEvs (setMem m s)

/-- **Arm thread steps with precise labels** (`ProgE2E.ATStep` restricted). -/
def ATStepP (P : Policy) : TSem AState AKind ClifThread.BVal := fun t evs t' =>
  t'.1 = t.1 ∧ ∃ l, TStep P t.1 (t.2.1, t.2.2) l (t'.2.1, t'.2.2) ∧ Precise t.2.1 l ∧
    evs = l.evs.map convEv

theorem atStep_of_P {P : Policy} {t t' : AState} {evs : List (Ev AKind ClifThread.BVal)}
    (h : ATStepP P t evs t') : ATStep P t evs t' := by
  obtain ⟨h1, l, hs, -, he⟩ := h
  exact ⟨h1, l, hs, he⟩

theorem runs_of_P {P : Policy} {PA : Traces AState AKind ClifThread.BVal} (h : PA.Runs (ATStepP P)) :
    PA.Runs (ATStep P) :=
  fun i hi j hj => atStep_of_P (h i hi j hj)

/-- A step's read events hold the bytes of its memory. -/
theorem agrees_stepEvs (s : ArmState) : Agrees (stepEvs s) s.mem := by
  unfold stepEvs
  split
  · split
    · exact VCodeThread.agrees_instEvs _ s
    · unfold errEvs; split
      · split
        · intro e he hr; simp only [List.mem_singleton] at he; subst he; cases hr
        · exact VCodeThread.agrees_nil _
      · exact VCodeThread.agrees_nil _
  · exact VCodeThread.agrees_nil _

/-- **Precise labels are receptive**: for every memory `m` the environment may provide, the
`stepi` thread steps with the precise label `stepEvs (setMem m s)` (reading `m`'s bytes), unless
it is a store exclusive the policy does not let succeed. -/
theorem exists_precise_step (P : Policy) (s : ArmState) (mon : Mon) (m : Memory)
    (hst : ∀ rel rs rn, cls s = .stx rel rs rn → P.succ mon) :
    ∃ t', TStep P stepi (s, mon) ⟨stepEvs (setMem m s), false⟩ t' ∧
      Precise s ⟨stepEvs (setMem m s), false⟩ ∧ Agrees (stepEvs (setMem m s)) m := by
  have hl := len_stepEvs (setMem m s)
  have hn := n_stepEvs (setMem m s)
  have hag : Agrees (stepEvs (setMem m s)) (applyR (stepEvs (setMem m s)) s.mem) :=
    agrees_applyR hl hn _
  have hk := kindsOk_stepEvs (setMem m s)
  rw [cls_setMem] at hk
  exact ⟨_, .exec hk hag (footprint_of_setMem (footprint_stepi _) hag) hst, .inr ⟨m, rfl⟩,
    agrees_stepEvs (setMem m s)⟩

end Concurrency.ArmPrecise
