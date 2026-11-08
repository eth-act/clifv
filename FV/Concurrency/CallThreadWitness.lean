import FV.Concurrency.CallThread
import FV.Concurrency.ArmAllocEntryWitness
import FV.Concurrency.ArmProgram

/-!
# Non-vacuity of the thread level from the ABI entry and of the callee contract (T2h, #311)

On the compiled `atomic_load` (`RealizeCompiled.WitnessL.RAL`, CLIF entry state `csL`):

* `compiledE_L`: every premise of `CallThread.CompiledE`;
* `thread_load_entry`: `thread_compiled_entry` on the precise run from the ABI entry through the
  `ldar` (`run_load_entry`);
* `armStepX_program`, `step_programL` (the activation's machine keeps the program),
  `noStxL` (no word of the function is a store exclusive with release: a check), and
  **`funReal_load`**: `funReal_callee` for the compiled `atomic_load` entered under any suspended
  callers `ext`, in any machine that is `RAL.step` on the states holding its program.
-/

namespace Concurrency.CallThread.Witness

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot RealizeCompiled RealizeCompiled.WitnessL

/-- **Every premise of `CompiledE`** for the compiled `atomic_load`. -/
theorem compiledE_L (env : Clif.Env) (p : Clif.Program) : CompiledE env p RAL csL := by
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRL abiRL bodyRL
  exact ⟨wfRL, entry_premises.2.1, rfl, ⟨_, abiRL⟩, (compiled_ofL hq hA env p).front, probeF_RL⟩

/-- **`thread_compiled_entry` on the compiled `atomic_load`**, on the precise run from its ABI
entry through its `ldar`. -/
theorem thread_load_entry (env : Clif.Env) (p : Clif.Program) :
    ∃ (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
      PRun Policy.arm RAL.step (OkPriv RAL) (RAL.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
      e.k = .acqR ∧ e.n = 8 ∧ e.addr = 0 ∧
      ∃ (k : Nat) (trS : List (List (Prog.Ev SKind BVal))) (t : TState)
        (ψ : Nat × Nat → Nat × Nat), k ≤ (lsP ++ [(⟨[e], false⟩ : Lab)]).length ∧
        ClifCStepTerm.CRun env p (.run csL) trS t ∧
        Refines Maps (PrivA RAL) (MonPair (evTr ((lsP ++ [(⟨[e], false⟩ : Lab)]).take k))) trS
          (conv (evTr ((lsP ++ [(⟨[e], false⟩ : Lab)]).take k))) ψ ∧
        (k = (lsP ++ [(⟨[e], false⟩ : Lab)]).length ∨ IselThread.Stop env p t ∨
          DoneBy RAL ((lsP ++ [(⟨[e], false⟩ : Lab)]).take k)) := by
  obtain ⟨lsP, e, t', -, hr, hk, hn, ha, -⟩ := run_load_entry
  exact ⟨lsP, e, t', hr, hk, hn, ha, thread_compiled_entry (compiledE_L env p) hr⟩

/-! ## The callee contract -/

/-- The machine of an activation keeps the program when its hooks do. -/
theorem armStepX_program {X : ExtSem} {H : ArmHooks} {fa : FnAsm}
    (hH : ∀ d s, (H.call d s).program = s.program)
    (hT : ∀ n r s, (H.tls n r s).program = s.program) (s : ArmState) :
    (ArmStepX X H fa s).program = s.program := by
  unfold ArmStepX
  dsimp only
  split <;> simp only [hH, hT, w_program, stepi_program]

theorem step_programL (s : ArmState) : (RAL.step s).program = s.program :=
  armStepX_program (fun _ _ => rfl) (fun _ _ _ => rfl) s

/-- A word that does not decode to a store exclusive with release. -/
def wordNoStxB (w : BitVec 32) : Bool :=
  match decode_raw_inst w with
  | some (.LDST (.Reg_exclusive i)) => !(decide (i.ord ≠ 1#1) && decide (i.L ≠ 1#1) &&
      decide (i.o0 = 1#1))
  | _ => true

theorem noStx_wordsL : (RAL.s0.program).all (fun q => wordNoStxB q.2) = true := by
  native_decide

theorem find?_mem {α β : Type} [DecidableEq α] : ∀ {m : List (α × β)} {a : α} {b : β},
    Map.find? m a = some b → ∃ a', (a', b) ∈ m
  | [], _, _, h => by simp [Map.find?] at h
  | (a0, b0) :: m, a, b, h => by
    simp only [Map.find?] at h
    split at h
    · cases h; exact ⟨a0, List.mem_cons_self⟩
    · obtain ⟨a', h'⟩ := find?_mem h
      exact ⟨a', List.mem_cons_of_mem _ h'⟩

/-- **No state of the compiled `atomic_load`'s program is at a store exclusive with release.** -/
theorem noStxL (s : ArmState) (hs : s.program = RAL.s0.program) (rs rn : BitVec 5) :
    cls s ≠ .stx true rs rn := by
  intro hc
  unfold cls at hc
  cases hd : decodeAt s with
  | none => rw [hd] at hc; cases hc
  | some ai =>
    rw [hd] at hc
    have hw : ∃ w, fetch_inst (r .PC s) s = some w ∧ decode_raw_inst w = some ai := by
      unfold decodeAt at hd
      split at hd
      · exact ⟨_, by assumption, hd⟩
      · cases hd
    obtain ⟨w, hf, hdw⟩ := hw
    rw [fetch_inst_from_program, hs] at hf
    obtain ⟨a', hmem⟩ := find?_mem hf
    have hok := List.all_eq_true.mp noStx_wordsL _ hmem
    simp only [wordNoStxB, hdw] at hok
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i =>
        simp only at hc
        split at hc
        · split at hc <;> cases hc
        · split at hc
          · cases hc
          · rename_i h1 h2
            simp only [Cls.stx.injEq] at hc
            simp_all
      | _ => cases hc
    | BR i =>
      cases i <;> simp only at hc
      all_goals (try split at hc) <;> (try split at hc) <;> cases hc
    | _ => cases hc

/-- **`funReal_callee` for the compiled `atomic_load`** (module doc). -/
theorem funReal_load (env : Clif.Env) (p : Clif.Program)
    (ext : List (Clif.Frame × List Clif.ValueId)) {M : ArmState → ArmState}
    (hM : ∀ s, s.program = RAL.s0.program → M s = RAL.step s) (mon : Mon) :
    CallCompose.FunReal env p (PrivA RAL) M (OkPriv RAL) (fun _ _ _ _ => False)
      (CalleeEnd env p RAL ext) (RAL.s0, mon) (.run (ClifLift.pushC ext csL)) :=
  funReal_callee (compiledE_L env p) ext hM (fun s hs => (step_programL s).trans hs)
    (fun mon ls t' hr => xClosed_runs (xClosed_noStx (π := RAL.s0.program)
      (fun s hs => (step_programL s).trans hs) noStxL rfl hr)) mon

end Concurrency.CallThread.Witness
