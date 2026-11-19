import FV.Opt.Proof.SemSimMU
import FV.Opt.Proof.ConstPhiWitness

/-!
# Non-vacuity of the memory-aware simulations (#1119)

Constant-phi removal's witness pair (`Opt.ConstPhi.Witness.fwd`/`fwd'`, two different functions)
is related by `FunSimMU` (`fwd_simMU`, from `FunSimU.toMU`). The one-function programs `p`/`q`
are related pointwise (`pq_simMU`); for every argument and memory, `fwd`'s entry state has an
`SRU`-related target state (`entry_sru`), so `runLoopX_refinesMU` applies (`fwd_refinesMU`). The
source run returns its argument (`p_returns`), hence so does the target run (`q_returns`).
-/

namespace Opt.SemSimMWitness

open Clif Opt.ConstPhi.Witness

/-- **`FunSimMU` relates two different functions.** -/
theorem fwd_simMU : FunSimMU fwd fwd' := fwd_simU.toMU

/-- `FunSimMU.trans` and `FunSimMU.refl` compose with it. -/
theorem fwd_simMU_trans : FunSimMU fwd fwd' := (FunSimMU.refl fwd).trans (fwd_simMU.trans
  (FunSimMU.refl fwd'))

def p : Program := { funcs := [fwd] }

def q : Program := { funcs := [fwd'] }

theorem pq_simMU : FunsSimMU p.funcs q.funcs := .cons fwd_simMU .nil

theorem keeps : EnvKeepsSymbolsX ({} : XEnv) := fun _ _ h => by cases h

/-- `fwd`'s entry block. -/
def b0 : Block := { id := 0, params := [(0, .i64)], term := .jump ⟨1, [0]⟩ }

theorem fwd_entry : fwd.entry? = some b0 := rfl

/-- `fwd`'s entry state with argument `v` and memory `m`. -/
def xs (v : BitVec 64) (m : Mem) : XState :=
  ⟨⟨⟨fwd, Regs.empty.set 0 ⟨.i64, v⟩, [], b0.body, b0.term⟩, [], m⟩, []⟩

theorem entry_sru (v : BitVec 64) (m : Mem) : ∃ xs', SRU m.symbols (xs v m) xs' := by
  obtain ⟨R, hR, hent⟩ := fwd_simU.sim m.symbols
  obtain ⟨b', -, -, hr⟩ := hent b0 fwd_entry
  exact ⟨⟨⟨⟨fwd', Regs.empty.set 0 ⟨.i64, v⟩, [], b'.body, b'.term⟩, [], m⟩, []⟩, rfl, rfl,
    ⟨R, hR, .inl (hr [⟨.i64, v⟩] _ [] rfl rfl rfl)⟩, .nil _⟩

/-- **`runLoopX_refinesMU` applies to a concrete program pair.** -/
theorem fwd_refinesMU (v : BitVec 64) (m : Mem) (n : Nat) :
    ∃ xs', SRU m.symbols (xs v m) xs' ∧
      ∃ n', XOutcomeRefines (runLoopX {} p n (xs v m)) (runLoopX {} q n' xs') := by
  obtain ⟨xs', h⟩ := entry_sru v m
  exact ⟨xs', h, runLoopX_refinesMU keeps pq_simMU n _ _ h⟩

/-- The source run returns its argument. -/
theorem p_returns (v : BitVec 64) : ∃ m', runLoopX {} p 2 (xs v {}) = .returned [⟨.i64, v⟩] m' :=
  ⟨_, rfl⟩

/-- Hence the related target run returns it too. -/
theorem q_returns (v : BitVec 64) : ∃ xs' n' m', SRU (({} : Mem).symbols) (xs v {}) xs' ∧
    runLoopX {} q n' xs' = .returned [⟨.i64, v⟩] m' := by
  obtain ⟨xs', h, n', hr⟩ := fwd_refinesMU v {} 2
  obtain ⟨m', hm⟩ := p_returns v
  exact ⟨xs', n', m', h, hr.1 _ _ hm⟩

end Opt.SemSimMWitness
