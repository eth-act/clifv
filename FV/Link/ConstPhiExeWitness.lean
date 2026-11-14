import FV.Link.ConstPhiExe
import FV.Opt.Proof.ConstPhiWitness
import FV.E2E.LegalOptX

/-!
# Non-vacuity of the linked composition of constant-phi removal (#990)

The input `S` has one function, the text of `Opt.ConstPhi.Witness.fwd` (`block1(v1)` receives
only `v0`). `FnInput.cp` prints its constant-phi removal `fwd'` and that text parses back to it
(`fi_cp_func`, `cp_changed`), so `S.cp` really differs from `S`. `cp_lift` applies with every
premise discharged: every run of `S.cp`'s program from `fwd'`'s entry on `5` that returns
returns `[5]` (`cp_runs`), hence so does every run of `S`'s program from `fwd`'s entry
(`source_returns`).
-/

namespace Link.ConstPhiExeWitness

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes Backend LinkSpec
open Opt.ConstPhi.Witness (fwd fwd')

def text : String :=
  "function %fwd(i64) -> i64 {\nblock0(v0: i64):\n    jump block1(v0)\n\nblock1(v1: i64):\n    return v1\n}\n"

def fi : FnInput := { clif := text, ra := "" }

def S : LinkSpec :=
  { funcs := [fi], names := ["fwd"], sizes := [1], outside := [], symNames := [], R := 4096 }

theorem fi_func : fi.func = fwd := by native_decide -- witness: native_decide

theorem fi_cp_func : fi.cp.func = fwd' := by native_decide -- witness: native_decide

theorem cp_changed : (fi.cp.clif == fi.clif) = false := by native_decide -- witness: native_decide

theorem prog_S : prog S.input = { funcs := [fi.func] } := by
  rw [prog_input]; rfl

theorem prog_Scp : prog S.cp.input = { funcs := [fi.cp.func] } := by
  rw [prog_input]; rfl

theorem func_S : (prog S.input).func? "fwd" = some fwd := by
  rw [prog_S, fi_func]; rfl

theorem func_Scp : (prog S.cp.input).func? "fwd" = some fwd' := by
  rw [prog_Scp, fi_cp_func]; rfl

def regs0 : Clif.Regs := (Clif.Regs.empty.setMany [0] [⟨.i64, 5⟩]).getD Clif.Regs.empty

/-- The entry of `fwd` on `5`. -/
def cs0 : Clif.State :=
  ⟨{ func := fwd, regs := regs0, slots := [], body := [], term := .jump ⟨1, [0]⟩ }, [],
    Clif.Mem.empty⟩

/-- The entry of `fwd'` on `5`. -/
def cs1 : Clif.State :=
  ⟨{ func := fwd', regs := regs0, slots := [], body := [], term := .jump ⟨1, []⟩ }, [],
    Clif.Mem.empty⟩

theorem entry0 : ClifEntry fwd [⟨.i64, 5⟩] cs0 :=
  ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem entry1 : ClifEntry fwd' [⟨.i64, 5⟩] cs1 :=
  ⟨rfl, rfl, rfl, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The claim: a return returns `[5]`. -/
def Ret5 (o : Clif.Outcome) : Prop := ∀ v M, o = .returned v M → v = [⟨.i64, 5⟩]

/-- **Every run of `S.cp`'s program from `fwd'`'s entry that returns returns `[5]`.** -/
theorem cp_runs (m : Nat) : Ret5 (Clif.runLoop Clif.Rust.env (prog S.cp.input) m cs1) := by
  rcases m with _ | _ | m
  · intro v M h; cases h
  · intro v M h
    have : Clif.runLoop Clif.Rust.env (prog S.cp.input) 1 cs1 = .outOfFuel := rfl
    rw [this] at h; cases h
  · intro v M h
    have : Clif.runLoop Clif.Rust.env (prog S.cp.input) (m + 2) cs1 =
        .returned [⟨.i64, 5⟩] Clif.Mem.empty := rfl
    rw [this] at h; cases h; rfl

/-- **`cp_lift` applies**: every run of `S`'s program from `fwd`'s entry on `5` that returns
returns `[5]`. -/
theorem source_returns (k : Nat) : Ret5 (Clif.runLoop Clif.Rust.env (prog S.input) k cs0) :=
  cp_lift (S := S) E2E.RustSyms.envKeepsSymbols_env func_S func_Scp entry0 entry1 rfl rfl rfl
    cp_runs (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) k

end Link.ConstPhiExeWitness
