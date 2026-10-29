module

public import FV.Clif.Run

@[expose] public section

/-!
# Memory-access traps of `Clif.run` (A3, #412, slice F2)

`docs/plans/memfault.md`. `Clif.run` is unchanged: an access whose bytes are not inside one live
allocation traps with its flags' trap code (`Mem.checkAccess`; `notrap` makes it `stuck`). This
file names that event so that the theorems can take premises about it:

* `Access fr inst a n`: the next statement's instruction `inst` (a load, store or atomic) accesses
  `[a, a + n)` in the frame `fr`;
* **`MemTrapAt env p s c a n`**: the step of `s` traps with `c` at a memory instruction whose
  access `[a, a + n)` is outside every live allocation;
* `memTrapInst`: the instructions whose memory trap the backend theorems refine, `atomic_rmw` and
  `atomic_cas` (on the measured cg_clif corpora every `load`, `store`, `atomic_load` and
  `atomic_store` is `notrap`, the plan's "What cg_clif emits");
* `evalInst_atomicRmw_trap`, `evalInst_atomicCas_trap`: such an instruction traps exactly at an
  aligned address outside the allocations, with its flags' code; `memTrapAt_of_trapped`: a
  trapping step at a `memTrapInst` statement is a `MemTrapAt`;
* `evalInst_notrap`: a `notrap` access never traps (it is `stuck` out of bounds).

The witness (`FV/Clif/MemTrapWitness.lean`) runs an `atomic_rmw` at address 0: it traps
`heap_oob`.
-/

namespace Clif

/-- **The access of a memory instruction** in the frame `fr`: `inst` reads or writes
`[a, a + n)` (the address operand defined in `fr`). -/
inductive Access (fr : Frame) : Inst → Nat → Nat → Prop
  | load {op ty fl p off pv} : fr.get p = .ok pv →
      Access fr (.load op ty fl p off) (effAddr pv off) (op.size ty)
  | store {op ty fl x p off pv} : fr.get p = .ok pv →
      Access fr (.store op ty fl x p off) (effAddr pv off) (op.size ty)
  | atomicRmw {op ty fl p x pv} : fr.get p = .ok pv →
      Access fr (.atomicRmw op ty fl p x) (effAddr pv 0) ty.bytes
  | atomicCas {ty fl p e x pv} : fr.get p = .ok pv →
      Access fr (.atomicCas ty fl p e x) (effAddr pv 0) ty.bytes
  | atomicLoad {ty fl p pv} : fr.get p = .ok pv →
      Access fr (.atomicLoad ty fl p) (effAddr pv 0) ty.bytes
  | atomicStore {ty fl x p pv} : fr.get p = .ok pv →
      Access fr (.atomicStore ty fl x p) (effAddr pv 0) ty.bytes

/-- **A memory trap at `s`**: the step of `s` traps with `c`, and the next statement is a memory
instruction whose access `[a, a + n)` is outside every live allocation of `s.mem`. -/
def MemTrapAt (env : Env) (p : Program) (s : State) (c : TrapCode) (a n : Nat) : Prop :=
  step env p s = .trapped c ∧ s.mem.valid a n = false ∧
    ∃ st rest, s.frame.body = st :: rest ∧ Access s.frame st.inst a n

/-- **The instructions whose memory trap the backend theorems refine**: `atomic_rmw` and
`atomic_cas` (lowered to the LL/SC loops, whose first access is the `ldaxr` of the address). -/
def memTrapInst : Inst → Bool
  | .atomicRmw .. | .atomicCas .. => true
  | _ => false

/-! ## Trapping accesses -/

theorem res_bind_eq_trap {α β : Type} {x : Res α} {f : α → Res β} {c : TrapCode}
    (h : (x >>= f) = .trap c) : x = .trap c ∨ ∃ a, x = .ok a ∧ f a = .trap c := by
  cases x with
  | ok a => exact .inr ⟨a, rfl, h⟩
  | trap c' => exact .inl (by simpa using h)
  | stuck m => cases h

theorem Frame.get_ne_trap (fr : Frame) (x : ValueId) (c : TrapCode) : fr.get x ≠ .trap c := by
  unfold Frame.get
  cases fr.regs x <;> simp [Res.ofOption]

theorem Frame.getAs_ne_trap (fr : Frame) (x : ValueId) (ty : Ty) (c : TrapCode) :
    fr.getAs x ty ≠ .trap c := by
  intro h
  unfold Frame.getAs at h
  rcases res_bind_eq_trap h with h | ⟨v, -, h⟩
  · exact fr.get_ne_trap x c h
  · cases hv : v.as? ty <;> rw [hv] at h <;> cases h

theorem Res.check_ne_trap (b : Bool) (msg : String) (c : TrapCode) : Res.check b msg ≠ .trap c := by
  cases b <;> simp

theorem Res.ofOption_ne_trap {α : Type} (msg : String) (o : Option α) (c : TrapCode) :
    Res.ofOption msg o ≠ .trap c := by
  cases o <;> simp

/-- `checkAccess` traps exactly out of bounds, with the flags' code. -/
theorem Mem.checkAccess_trap {m : Mem} {fl : MemFlags} {a n : Nat} {c : TrapCode}
    (h : m.checkAccess fl a n = .trap c) : m.valid a n = false ∧ fl.trapCode = some c := by
  unfold Mem.checkAccess at h
  split at h
  · split at h <;> cases h
  · rename_i hv
    refine ⟨by simpa using hv, ?_⟩
    split at h
    · rename_i c' hc
      cases h
      exact hc
    · cases h

theorem Mem.checkAccess_valid {m : Mem} {fl : MemFlags} {a n : Nat} (hv : m.valid a n = true)
    (c : TrapCode) : m.checkAccess fl a n ≠ .trap c := by
  intro h
  have := (Mem.checkAccess_trap h).1
  rw [hv] at this
  cases this

theorem Mem.load_trap {m : Mem} {fl : MemFlags} {a n w : Nat} {c : TrapCode}
    (h : m.load fl a n w = .trap c) : m.valid a n = false ∧ fl.trapCode = some c := by
  unfold Mem.load at h
  rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
  · exact Mem.checkAccess_trap h
  · exact absurd h (Res.ofOption_ne_trap _ _ c)

theorem Mem.store_trap {m : Mem} {fl : MemFlags} {a n : Nat} {w : Nat} {x : BitVec w}
    {c : TrapCode} (h : m.store fl a n x = .trap c) : m.valid a n = false ∧ fl.trapCode = some c := by
  unfold Mem.store at h
  rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
  · exact Mem.checkAccess_trap h
  · rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
    · exact absurd h (Res.check_ne_trap _ _ c)
    · cases h

/-- **A trapping `atomic_rmw`**: its address is aligned and outside every live allocation, and
the trap code is the flags'. -/
theorem evalInst_atomicRmw_trap {fr : Frame} {cm : Mem} {op : AtomicRmwOp} {ty : Ty}
    {fl : MemFlags} {p x : ValueId} {c : TrapCode}
    (h : evalInst fr cm (.atomicRmw op ty fl p x) = .trap c) :
    ∃ pv, fr.get p = .ok pv ∧ effAddr pv 0 % ty.bytes = 0 ∧
      cm.valid (effAddr pv 0) ty.bytes = false ∧ fl.trapCode = some c := by
  simp only [evalInst] at h
  rcases res_bind_eq_trap h with h | ⟨pv, hpv, h⟩
  · exact absurd h (fr.get_ne_trap p c)
  rcases res_bind_eq_trap h with h | ⟨a, -, h⟩
  · exact absurd h (fr.getAs_ne_trap x ty c)
  rcases res_bind_eq_trap h with h | ⟨_, hal, h⟩
  · exact absurd h (Res.check_ne_trap _ _ c)
  have hal' : effAddr pv 0 % ty.bytes = 0 := by
    unfold Res.check at hal
    split at hal
    · rename_i hb; simpa using hb
    · cases hal
  rcases res_bind_eq_trap h with h | ⟨old, hl, h⟩
  · obtain ⟨hv, hc⟩ := Mem.load_trap h
    exact ⟨pv, hpv, hal', hv, hc⟩
  rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
  · obtain ⟨hv, hc⟩ := Mem.store_trap h
    exact ⟨pv, hpv, hal', hv, hc⟩
  · cases h

/-- **A trapping `atomic_cas`**: as `evalInst_atomicRmw_trap`. -/
theorem evalInst_atomicCas_trap {fr : Frame} {cm : Mem} {ty : Ty} {fl : MemFlags}
    {p e x : ValueId} {c : TrapCode} (h : evalInst fr cm (.atomicCas ty fl p e x) = .trap c) :
    ∃ pv, fr.get p = .ok pv ∧ effAddr pv 0 % ty.bytes = 0 ∧
      cm.valid (effAddr pv 0) ty.bytes = false ∧ fl.trapCode = some c := by
  simp only [evalInst] at h
  rcases res_bind_eq_trap h with h | ⟨pv, hpv, h⟩
  · exact absurd h (fr.get_ne_trap p c)
  rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
  · exact absurd h (fr.getAs_ne_trap e ty c)
  rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
  · exact absurd h (fr.getAs_ne_trap x ty c)
  rcases res_bind_eq_trap h with h | ⟨_, hal, h⟩
  · exact absurd h (Res.check_ne_trap _ _ c)
  have hal' : effAddr pv 0 % ty.bytes = 0 := by
    unfold Res.check at hal
    split at hal
    · rename_i hb; simpa using hb
    · cases hal
  rcases res_bind_eq_trap h with h | ⟨old, hl, h⟩
  · obtain ⟨hv, hc⟩ := Mem.load_trap h
    exact ⟨pv, hpv, hal', hv, hc⟩
  split at h
  · rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
    · obtain ⟨hv, hc⟩ := Mem.store_trap h
      exact ⟨pv, hpv, hal', hv, hc⟩
    · cases h
  · simp at h

/-- **A trapping memory statement is a memory trap** (`memTrapInst`: `atomic_rmw`,
`atomic_cas`): its access is aligned, outside every live allocation, the code the flags'. -/
theorem memTrapAt_of_trapped {env : Env} {p : Program} {s : State} {c : TrapCode} {st : Stmt}
    {rest : List Stmt} (hb : s.frame.body = st :: rest) (hm : memTrapInst st.inst = true)
    (h : step env p s = .trapped c) :
    ∃ a n fl, MemTrapAt env p s c a n ∧ a % n = 0 ∧ fl.trapCode = some c ∧
      ((∃ op ty q x, st.inst = .atomicRmw op ty fl q x ∧ n = ty.bytes) ∨
        ∃ ty q e x, st.inst = .atomicCas ty fl q e x ∧ n = ty.bytes) := by
  have hstep := h
  rw [step_inst env p s st rest hb (fun fn args e => by rw [e] at hm; cases hm)
    (fun sig callee args e => by rw [e] at hm; cases hm)] at h
  cases he : evalInst s.frame s.mem st.inst with
  | ok r => rw [he] at h; simp only [StepResult.ofRes, continueWith] at h; split at h <;> cases h
  | stuck m => rw [he] at h; cases h
  | trap c' =>
    rw [he] at h
    simp only [StepResult.ofRes, StepResult.trapped.injEq] at h
    subst h
    cases hi : st.inst with
    | atomicRmw op ty fl q x =>
      rw [hi] at he
      obtain ⟨pv, hpv, hal, hv, hc⟩ := evalInst_atomicRmw_trap he
      exact ⟨_, _, fl, ⟨hstep, hv, st, rest, hb, hi ▸ .atomicRmw hpv⟩, hal, hc,
        .inl ⟨op, ty, q, x, rfl, rfl⟩⟩
    | atomicCas ty fl q e x =>
      rw [hi] at he
      obtain ⟨pv, hpv, hal, hv, hc⟩ := evalInst_atomicCas_trap he
      exact ⟨_, _, fl, ⟨hstep, hv, st, rest, hb, hi ▸ .atomicCas hpv⟩, hal, hc,
        .inr ⟨ty, q, e, x, rfl, rfl⟩⟩
    | _ => rw [hi] at hm; cases hm

/-! ## `notrap` accesses never trap -/

/-- The flags of a memory instruction (`none` for the other instructions). -/
def Inst.memFlags? : Inst → Option MemFlags
  | .load _ _ fl _ _ | .store _ _ fl _ _ _ | .atomicRmw _ _ fl _ _ | .atomicCas _ fl _ _ _
  | .atomicLoad _ fl _ | .atomicStore _ fl _ _ => some fl
  | _ => none

theorem Mem.load_notrap {m : Mem} {fl : MemFlags} (hn : fl.trapCode = none) (a n w : Nat)
    (c : TrapCode) : m.load fl a n w ≠ .trap c := by
  intro h
  have := (Mem.load_trap h).2
  rw [hn] at this
  cases this

theorem Mem.store_notrap {m : Mem} {fl : MemFlags} (hn : fl.trapCode = none) (a n : Nat) {w : Nat}
    (x : BitVec w) (c : TrapCode) : m.store fl a n x ≠ .trap c := by
  intro h
  have := (Mem.store_trap h).2
  rw [hn] at this
  cases this

/-- **A `notrap` access never traps**: a load, store or atomic whose flags are `notrap` does not
step to a trap (out of bounds it is `stuck`). -/
theorem evalInst_notrap {fr : Frame} {cm : Mem} {inst : Inst} {fl : MemFlags}
    (hf : inst.memFlags? = some fl) (hn : fl.trapCode = none) (c : TrapCode) :
    evalInst fr cm inst ≠ .trap c := by
  intro h
  cases inst <;> simp only [Inst.memFlags?, reduceCtorEq, Option.some.injEq] at hf
  all_goals subst hf
  all_goals simp only [evalInst] at h
  all_goals
    repeat
      first
      | (rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
         · first
           | exact absurd h (Frame.get_ne_trap _ _ c)
           | exact absurd h (Frame.getAs_ne_trap _ _ _ c)
           | exact absurd h (Res.check_ne_trap _ _ c)
           | exact absurd h (Mem.load_notrap hn _ _ _ c)
           | exact absurd h (Mem.store_notrap hn _ _ _ c))
  all_goals first
    | cases h
    | (split at h
       · rcases res_bind_eq_trap h with h | ⟨_, -, h⟩
         · exact absurd h (Mem.store_notrap hn _ _ _ c)
         · cases h
       · simp at h)

end Clif
