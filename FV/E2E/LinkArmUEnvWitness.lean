module

public import FV.E2E.LinkArmUEnv
public import FV.E2E.NonVacuityLink

@[expose] public section

/-!
# Non-vacuity of the external semantics with unwinding (S10f, #233)

On `E2E.LinkWitness.L` (`FV/E2E/NonVacuityLink.lean`: a linked program of 18 compiled functions
with indirect calls, slots and outgoing arguments, whose `LinkSys.Ok` holds, `L_ok`), extended to
a `LinkSysU` whose base callees do not raise (`Ub`, `XRb` none; the base CLIF environment
`Clif.Env.empty`, without unwinding): the default callee runs with unwinding are whole-program
runs with unwinding (`crunOkX_std`, from `Clif.runLoopX_linkN`, with the indirect calls' scope
`Clif.IndScope.toX`), and the exclusivity of every activation's callees (`XU_excl`) holds.
`L_ok` rests on executable checks decided by `native_decide`.
-/

namespace E2E.LinkArmUEnvWitness

open Backend Backend.Proof LinkWitness

/-- `LinkWitness.L` with base callees that do not raise. -/
def LU : LinkSysU :=
  { L (Img P A) with Ub := Unw.UnwHooks.none, envX := (L (Img P A)).base.toX, XRb := XRaise.none }

theorem LU_ok : LU.Ok := L_ok (Img P A) fun _ h => h

/-- **The default callee runs with unwinding of the witness are whole-program runs.** -/
theorem crunOkX : LU.stdX.CrunOkX :=
  LU.crunOkX_std LU_ok fun g hg hn => (LU_ok.indScope g hg hn).toX

/-- **The witness's activations' callees are exclusive** (a normal return does not raise). -/
theorem excl (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (d : Option String) (uses : List CV) (w : Arm.ArmState)
    (hx : (LU.XU κ M g F).call d uses w ≠ none) : (LU.XRU κ M g F).raise d uses w = none :=
  LU.XU_excl (fun _ _ _ _ _ => rfl) d uses w hx

end E2E.LinkArmUEnvWitness
