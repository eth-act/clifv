import FV.Concurrency.VCodeAddr
import FV.Backend.Proof.LoopRun

/-!
# The addresses of the memory events of VCode's atomics (T2h, #311, layer 2a)

The atomics' events under `csem` (`VCodeThread.cEvs`) are at the access's address, of its size:

* `ldar_evs`/`stlr_evs`: `ldar`/`stlr` of the canonical allocation (`loadAcquire`/`storeRelease`
  with the address in x0) access `x0`, `ty.bytes` bytes;
* `fence_evs`: `dmb ish` has events of size 0 only;
* `rmwBody_evs`, `casHead_evs`, `casStore_evs` (`VCodeThread.casStore`): every event of the LL/SC loops' bodies is at
  `x25` (the address register), `ty.bytes` bytes.
-/

namespace Concurrency.VCodeAddr

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code

attribute [local csimp_rules] wmb_cast Arm.LDST.exec_reg_exclusive Insn.armFields.exclFields
  CTy.bits Arm.r_of_write_mem_bytes Arm.ldst_read Arm.read_mem_bytes_of_w

/-- Every event has address `a` and size `n`. -/
def AtA (a : BitVec 64) (n : Nat) (evs : List Ev) : Prop := ∀ e ∈ evs, e.addr = a ∧ e.n = n

set_option maxHeartbeats 4000000 in
theorem ldar_evs {ty : CTy} (hty : AtomTy ty) (env : Env) (tc : Option Clif.TrapCode) (s : ArmState) :
    AtA (Arm.r (.GPR 0#5) s) ty.bytes (linesEvs env [.ins (.ldar ty.bits (.x 1) (.x 0)) tc] s) := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · intro e he
    simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, exclEvs] at he
    rcases he with ⟨-, rfl⟩ | rfl <;> simp [CTy.bytes, CTy.bits]

set_option maxHeartbeats 4000000 in
theorem stlr_evs {ty : CTy} (hty : AtomTy ty) (env : Env) (tc : Option Clif.TrapCode) (s : ArmState) :
    AtA (Arm.r (.GPR 0#5) s) ty.bytes (linesEvs env [.ins (.stlr ty.bits (.x 1) (.x 0)) tc] s) := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · intro e he
    simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, exclEvs] at he
    rcases he with ⟨-, rfl⟩ | rfl <;> simp [CTy.bytes, CTy.bits]

theorem fence_evs (env : Env) (tc : Option Clif.TrapCode) (s : ArmState) :
    ∀ e ∈ linesEvs env [.ins .dmbish tc] s, e.n = 0 := by
  intro e he
  simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, fullBarrier] at he
  rcases he with ⟨-, rfl⟩ | rfl <;> rfl

/-- A prefix without memory kinds that runs: the events of `A ++ B` are those of `B` from the
prefix's end state. -/
theorem linesEvs_exec : ∀ {env : Env} {A : List Line} (B : List Line) {s s1 : ArmState},
    execLines env A s = some s1 → kinds A = [] →
    linesEvs env (A ++ B) s = linesEvs { env with pc := env.pc + 4 * A.length } B s1
  | env, [], B, s, s1, h, _ => by
    simp only [execLines, Option.some.injEq] at h; subst h
    simp
  | env, .ins i t :: A, B, s, s1, h, hk => by
    have hk1 : insnKind i = none := by
      simp only [kinds, List.filterMap_cons, lineKind] at hk
      split at hk
      · assumption
      · cases hk
    have hkA : kinds A = [] := by
      simp only [kinds, List.filterMap_cons, lineKind, hk1] at hk
      exact hk
    simp only [execLines] at h
    split at h
    · rename_i ai ha
      split at h
      · rename_i hpc
        have ih := linesEvs_exec (env := { env with pc := env.pc + 4 }) B h hkA
        simp only [List.cons_append, linesEvs, ha, hpc, ite_true, instEvs_none ha hk1,
          List.nil_append]
        rw [ih]
        simp only [List.length_cons]
        congr 1
        cases env; simp; omega
      · cases h
    · cases h
  | _, .label _ :: _, _, _, _, h, _ => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, _, h, _ => by simp [execLines] at h
  | _, .data _ :: _, _, _, _, h, _ => by simp [execLines] at h

theorem execLines_append : ∀ {env : Env} (A B : List Line) (s : ArmState),
    execLines env (A ++ B) s =
      (execLines env A s).bind (execLines { env with pc := env.pc + 4 * A.length } B)
  | env, [], B, s => by simp [execLines]
  | env, .ins i t :: A, B, s => by
    simp only [List.cons_append, execLines]
    split
    · split
      · rw [execLines_append A B]
        simp only [List.length_cons]
        congr 2
        cases env; simp; omega
      · rfl
    · rfl
  | _, .label _ :: _, _, _ => by simp [execLines]
  | _, .word _ _ :: _, _, _ => by simp [execLines]
  | _, .data _ :: _, _, _ => by simp [execLines]

/-- The first line of a run. -/
theorem exec_cons {env : Env} {i : Insn} {tc : Option Clif.TrapCode} {ls : List Line}
    {s t : ArmState} (h : execLines env (.ins i tc :: ls) s = some t) :
    ∃ ai, i.toArmInst env = .ok ai ∧ Arm.r .PC (Arm.exec_inst ai s) = Arm.r .PC s + 4#64 ∧
      execLines { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s) = some t ∧
      linesEvs env (.ins i tc :: ls) s =
        instEvs ai s ++ linesEvs { env with pc := env.pc + 4 } ls (Arm.exec_inst ai s) := by
  simp only [execLines] at h
  split at h
  · rename_i ai ha
    split at h
    · rename_i hpc
      exact ⟨ai, ha, hpc, h, by simp only [linesEvs, ha, hpc, ite_true]⟩
    · cases h
  · cases h

set_option maxHeartbeats 4000000 in
theorem ldaxr_evs {ty : CTy} (hty : AtomTy ty) {env : Env} {ai : ArmInst}
    (ha : (Insn.ldaxr ty.bits (.x 27) (.x 25)).toArmInst env = .ok ai) (s : ArmState) :
    AtA (Arm.r (.GPR 25#5) s) ty.bytes (instEvs ai s) := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    intro e he
    simp (config := {decide := true}) [instEvs, exclEvs] at he
    rcases he with ⟨-, rfl⟩ <;> simp [CTy.bytes, CTy.bits] <;> rfl

set_option maxHeartbeats 4000000 in
theorem stlxr_evs {ty : CTy} (hty : AtomTy ty) {env : Env} {rs : Reg} {ai : ArmInst}
    (hrs : rs = .x 26 ∨ rs = .x 28)
    (ha : (Insn.stlxr ty.bits (.x 24) rs (.x 25)).toArmInst env = .ok ai) (s : ArmState) :
    AtA (Arm.r (.GPR 25#5) s) ty.bytes (instEvs ai s) ∧
      Arm.r (.GPR 25#5) (Arm.exec_inst ai s) = Arm.r (.GPR 25#5) s := by
  rcases hty with rfl | rfl | rfl | rfl <;> rcases hrs with rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    refine ⟨fun e he => ?_, ?_⟩
    · simp (config := {decide := true}) [instEvs, exclEvs] at he
      rcases he with ⟨-, rfl⟩ <;> simp [CTy.bytes, CTy.bits] <;> rfl
    · simp (config := {decide := true}) [csimp_rules, Arm.r_of_w_different]

/-- **Every event of the `atomic_rmw` loop body is at x25, of the access size** (on a state from
which the body runs: its event-free middle keeps x25, `rmwBody_spec`). -/
theorem rmwBody_evs {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (e : Env) (t : ArmState) (herr : Arm.r .ERR t = .None) :
    AtA (Arm.r (.GPR 25#5) t) ty.bytes (linesEvs e (rmwLoopBody ty.bits op fl) t) := by
  obtain ⟨t', hrun, -, -, -, hfr, -, -⟩ := rmwBody_spec hty op fl e t herr
  have h25 : Arm.r (.GPR 25#5) t' = Arm.r (.GPR 25#5) t :=
    hfr _ (by simp) (by simp) (by simp)
  unfold rmwLoopBody at hrun ⊢
  simp only [List.singleton_append, List.cons_append, List.nil_append] at hrun ⊢
  obtain ⟨a1, ha1, -, hr1, he1⟩ := exec_cons hrun
  rw [he1]
  rw [execLines_append] at hr1
  cases hm : execLines { e with pc := e.pc + 4 } ((rmwLoopMid op ty.bits).map fun i => .ins i)
      (Arm.exec_inst a1 t) with
  | none => rw [hm] at hr1; cases hr1
  | some s2 =>
    rw [hm] at hr1
    simp only [Option.bind_some] at hr1
    obtain ⟨a2, ha2, -, hr2, he2⟩ := exec_cons hr1
    simp only [execLines, Option.some.injEq] at hr2
    rw [linesEvs_exec _ hm (kinds_rmwLoopMid op ty.bits), he2]
    simp only [linesEvs, List.append_nil]
    obtain ⟨hev2, hx2⟩ := stlxr_evs hty (by cases op <;> simp [rmwLoopStored]) ha2 s2
    have hs2 : Arm.r (.GPR 25#5) s2 = Arm.r (.GPR 25#5) t := by rw [← hx2, hr2, h25]
    intro ev hev
    rcases List.mem_append.mp hev with h | h
    · exact ldaxr_evs hty ha1 t ev h
    · rw [← hs2]; exact hev2 ev h

/-- Every event of the `atomic_cas` loop's head (`ldaxr; cmp`) is at x25. -/
theorem casHead_evs {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env) (t : ArmState)
    (herr : Arm.r .ERR t = .None) :
    AtA (Arm.r (.GPR 25#5) t) ty.bytes (linesEvs e (casLoopHead ty.bits fl) t) := by
  obtain ⟨t', hrun, -⟩ := casHead_spec hty fl e t herr
  unfold casLoopHead at hrun ⊢
  obtain ⟨a1, ha1, -, hr1, he1⟩ := exec_cons hrun
  rw [he1]
  have hc := linesEvs_exec ([] : List Line) hr1 (by
    simp only [kinds, List.filterMap_cons, List.filterMap_nil, lineKind, insnKind_casLoopCmp])
  simp only [List.append_nil] at hc
  rw [hc]
  simp only [linesEvs, List.append_nil]
  exact ldaxr_evs hty ha1 t

/-- The event of the `atomic_cas` loop's `stlxr` is at x25. -/
theorem casStore_evs {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env) (t : ArmState) :
    AtA (Arm.r (.GPR 25#5) t) ty.bytes (linesEvs e (casStore ty.bits fl) t) := by
  unfold casStore
  cases ha : (Insn.stlxr ty.bits (.x 24) (.x 28) (.x 25)).toArmInst e with
  | error _ => simp only [linesEvs, ha]; exact fun _ h => nomatch h
  | ok ai => rw [linesEvs_single ha]; exact (stlxr_evs hty (.inr rfl) ha t).1

end Concurrency.VCodeAddr
