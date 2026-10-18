import FV.Concurrency.Mapping

/-!
# LSE atomics (`has_lse`, T2g #305)

**Not emitted in our configuration.** cg_clif sets Cranelift's `has_lse` only through
`-Ctarget-cpu` (`native`, or a CPU preset; `rustc_codegen_cranelift/src/lib.rs`, `build_isa`;
`-Ctarget-feature` is ignored), and `cargo fv` passes none: every CLIF bundle says
`target aarch64 has_lse=0`. The Lean backend implements the non-LSE lowering only (`Backend.Isel`:
`use_lse` fails), and the stock-configured driver rejects `has_lse=1` for functions with an
LSE-lowered atomic (`FVTest/Backend/StockConfig.lean`, `usesLse`).

**What Cranelift emits with `has_lse`** (`isa/aarch64/lower.isle`, rules `use_lse`;
`inst/emit.rs`, `enc_acq_rel`/`enc_cas`, acquire and release bits set): `atomic_rmw` `add`, `sub`
(negated operand), `and` (complemented operand, `ldclral`), `or` (`ldsetal`), `xor` (`ldeoral`),
`smax`/`smin`/`umax`/`umin` become one `ld<op>al`; `atomic_cas` becomes `casal`; `nand` and `xchg`
keep the LL/SC loop.

**Memory model.** In `aarch64.cat` an `ld<op>al` or a successful `casal` is a read in `A` and a
write in `L` paired by `rmw` (`amo`), and a failed `casal` is its read in `A`: the same kinds and
pairing as a successful LL/SC iteration (`acqXR`, `relXW`; nothing in the model distinguishes
`lxsx` from `amo` pairs: the atomic axiom and `aob = rmw` are about `rmw`). So `lseKinds` maps
by Cranelift's table (`lse_maps`), and `Mapping.armv8_to_clif`/`armv8_to_clifF`,
`Mapping.armv8_drf_sc` and the program-level theorems apply to LSE code unchanged; the ATOM-INC
litmus executions (`FVTest/Concurrency/Litmus.lean`, `inc_*`) are also those of two `ldaddal`s.
-/

namespace Concurrency.Lse

/-- The `ld<op>al` operations Cranelift emits. -/
inductive LseOp where
  | add | clr | eor | set | smax | smin | umax | umin
  deriving DecidableEq, Repr

/-- The LSE instructions Cranelift emits for CLIF atomics with `has_lse`. -/
inductive LseInsn where
  /-- `ld<op>al` for `atomic_rmw` -/
  | ldOpAL (op : LseOp)
  /-- `casal` for `atomic_cas` -/
  | casAL
  deriving DecidableEq, Repr

/-- The events of an LSE instruction: an `ld<op>al` reads and writes; a `casal` reads, and
writes when the comparison succeeds (`ok`). -/
def lseKinds : LseInsn → Bool → List AKind
  | .ldOpAL _, _ => [.acqXR, .relXW]
  | .casAL, true => [.acqXR, .relXW]
  | .casAL, false => [.acqXR]

/-- The events of the CLIF statement (`ClifThread.evShape`): `atomic_rmw` its read and write,
`atomic_cas` its read, and its write when the comparison succeeds. -/
def clifKinds : LseInsn → Bool → List SKind
  | .ldOpAL _, _ => [.scR, .scW]
  | .casAL, true => [.scR, .scW]
  | .casAL, false => [.scR]

/-- **Cranelift's LSE lowering maps by the table** (`Maps`, the table of `Mapping.armv8_to_clif`). -/
theorem lse_maps (i : LseInsn) (ok : Bool) :
    (clifKinds i ok).length = (lseKinds i ok).length ∧
      ∀ (j : Nat) s a, (clifKinds i ok)[j]? = some s → (lseKinds i ok)[j]? = some a → Maps s a := by
  cases i <;> cases ok <;> refine ⟨rfl, fun j s a h1 h2 => ?_⟩ <;>
    rcases j with _ | _ | j <;> simp [clifKinds, lseKinds] at h1 h2 <;> subst h1 h2 <;> decide

end Concurrency.Lse
