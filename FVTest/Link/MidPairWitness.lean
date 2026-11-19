import FVTest.Backend.MidValPassWitness
import FV.Link.MidPair
import FV.Link.MidProg

/-! # Witness: the bundle decision and `Link.midProg` on a real pair (#1119, layer 2)

**Witness file** (`native_decide` allowed; not a compiler theorem). The pair of
`FVTest/Backend/MidValPassWitness.lean` (sha3 0.12.0's release build, dependency keccak,
`_RNxC6keccak12HbPukoXULhhU`): cg_clif's source function `fSrc` (`.unopt.clif`) and Cranelift's
optimised function `gOpt` (`.opt.clif`), which differ.

* `facts0`: `Link.midValidatedB [fSrc] [gOpt] = true` (what `lean-link` / `link-check` decide),
  `fSrc ≠ gOpt`, and the decidable facts of an entry state `cs0` of `fSrc`;
* `validated`: `Opt.MidVal.Validated [fSrc] [gOpt]` by `Link.midValidatedB_sound`;
* `midProg_applies`: `Link.midProg` instantiated on the one-function programs `P0 = [fSrc]`,
  `Q = [gOpt]`, the empty base environment (`Opt.EnvKeepsSymbols`), and the entry `cs0` of `fSrc`
  on zero arguments: every premise discharged, so its conclusion holds at every fuel.
-/

namespace FVTest.Link.MidPairWitness
open FVTest.Backend.MidValPassWitness (fSrc gOpt)
open E2E
set_option autoImplicit false

/-- The bundle's (unoptimised) one-function program. -/
def P0 : Clif.Program := { funcs := [fSrc] }

/-- The compiled (optimised) one-function program. -/
def Q : Clif.Program := { funcs := [gOpt] }

/-- Zero arguments of `fSrc`'s parameter types. -/
def args0 : List Clif.Val := fSrc.sig.params.map fun p => ⟨p.ty, 0⟩

/-- `fSrc`'s entry block. -/
def blk : Clif.Block := fSrc.entry?.getD default

/-- The registers of the entry block's parameters bound to `args0`. -/
def regs0 : Clif.Regs :=
  (Clif.Regs.empty.setMany (blk.params.map (·.1)) args0).getD Clif.Regs.empty

/-- An entry state of `fSrc` on `args0` (every slot at address 0, empty memory). -/
def cs0 : Clif.State :=
  ⟨⟨fSrc, regs0, fSrc.slots.map fun s => (s.1, 0), blk.body, blk.term⟩, [], Clif.Mem.empty⟩

/-- What `native_decide` evaluates: the decision on the pair, that the functions differ, the names
the programs look the functions up by, and the decidable facts of `cs0`'s entry. -/
def facts : Bool :=
  Link.midValidatedB P0.funcs Q.funcs && !decide (fSrc = gOpt) &&
  decide (P0.func? fSrc.name = some fSrc) && decide (Q.func? fSrc.name = some gOpt) &&
  decide (args0.map (·.ty) = fSrc.sig.params.map (·.ty)) &&
  decide (fSrc.entry? = some blk) && decide (blk.params.map (·.2) = args0.map (·.ty)) &&
  (Clif.Regs.empty.setMany (blk.params.map (·.1)) args0).isSome &&
  decide ((fSrc.slots.map fun s => (s.1, 0)).map (·.1) = fSrc.slots.map (·.1))

theorem facts0 : facts = true := by native_decide

theorem facts_spec :
    Link.midValidatedB P0.funcs Q.funcs = true ∧ fSrc ≠ gOpt ∧
    P0.func? fSrc.name = some fSrc ∧ Q.func? fSrc.name = some gOpt ∧
    ClifEntry fSrc args0 cs0 := by
  have h := facts0
  simp only [facts, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv, hne⟩, hf⟩, hg⟩, hsig⟩, hb⟩, hpar⟩, hset⟩, hslots⟩ := h
  have hreg : Clif.Regs.empty.setMany (blk.params.map (·.1)) args0 = some regs0 := by
    unfold regs0
    revert hset
    cases Clif.Regs.empty.setMany (blk.params.map (·.1)) args0 <;> simp
  exact ⟨hv, hne, hf, hg, ⟨rfl, rfl, hsig, ⟨blk, hb, rfl, rfl, hpar, hreg⟩, hslots⟩⟩

/-- The pair is validated (`Link.midValidatedB_sound`), and the functions differ. -/
theorem validated : Opt.MidVal.Validated P0.funcs Q.funcs ∧ fSrc ≠ gOpt :=
  ⟨Link.midValidatedB_sound facts_spec.1, facts_spec.2.1⟩

/-- The empty base environment keeps the symbols (it has no externs). -/
theorem keep_empty : Opt.EnvKeepsSymbols Clif.Env.empty := by
  intro name f h
  cases h

/-- **`Link.midProg` applies to the pair** with every premise discharged. -/
theorem midProg_applies (M : Nat) :
    ClifEntry gOpt args0 (midEntry gOpt cs0) ∧
      (midEntry gOpt cs0).frame.slots = cs0.frame.slots ∧ (midEntry gOpt cs0).mem = cs0.mem ∧
    (∀ vals cm, Clif.runLoop Clif.Env.empty P0 M cs0 = .returned vals cm →
      ∃ m, Clif.runLoop Clif.Env.empty Q m (midEntry gOpt cs0) = .returned vals cm) ∧
    (∀ c, Clif.runLoop Clif.Env.empty P0 M cs0 = .trapped c →
      ∃ m, Clif.runLoop Clif.Env.empty Q m (midEntry gOpt cs0) = .trapped c) :=
  Link.midProg validated.1 keep_empty facts_spec.2.2.1 facts_spec.2.2.2.1 facts_spec.2.2.2.2 M

end FVTest.Link.MidPairWitness
