import FV.E2E.ArmGprFoot
import FV.E2E.RegLevelMachine

/-!
# The frameless leaf's check on compiled code: no line but `ret` names `x29` or `x30` (#1028)

The decidable check `FnAsm.leafKeep` (and `FnAsm.gprKeep k`, `Insn.gprKeep k`) whose soundness
`E2E.RL.iterN_leafKeep` (`FV/E2E/RegLevelLeafKeep.lean`) proves: on a function that passes it,
every run of the activation keeps `x29` and `x30`. A frameless leaf returns with the `x29`/`x30` it
was entered with, so its register-level proof needs this of its body.
-/

namespace E2E

open Backend Backend.Proof

/-- The hooked lines whose step keeps `x_k`: the relocated address computations (`adrp` and the
GOT's `adrp` write their destination, which must not be `x_k`; the `ldr`/`add` halves and the TLS
descriptor `adrp` write only the pc). The calls (`bl`, `blr`, the TLS descriptor call) do not. -/
def _root_.Backend.Insn.hookedGprKeep (k : BitVec 5) : Insn → Bool
  | .adrpGot rd _ | .adrp rd _ _ => (rd.encZR.toOption.getD 31#5) != k
  | .ldrGotLo12 .. | .addLo12 .. | .adrpTlsDesc .. => true
  | _ => false

/-- **The machine's step at line `i` keeps `x_k`** (module doc). -/
def _root_.Backend.Insn.gprKeep (k : BitVec 5) (env : Env) (i : Insn) : Bool :=
  if i.hooked then i.hookedGprKeep k
  else match i with
    | .ret => true
    | _ => match i.toArmInst env with
      | .ok a => a.gprs.all (· != k)
      | .error _ => false

/-- **The check on compiled code**: every instruction line `j` of `fa` is `gprKeep k` at its
encoder environment (`RL.envOf`). -/
def _root_.Backend.FnAsm.gprKeep (k : BitVec 5) (fa : FnAsm) (lm : Std.HashMap Lbl Nat) : Bool :=
  (List.range fa.lines.toList.length).all fun j =>
    match fa.lines.toList[j]? with
    | some (.ins x _) => x.gprKeep k ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩
    | _ => true

/-- **The check of a frameless leaf**: no line but `ret` reads or writes `x29` or `x30`. -/
def _root_.Backend.FnAsm.leafKeep (fa : FnAsm) (lm : Std.HashMap Lbl Nat) : Bool :=
  fa.gprKeep 29#5 lm && fa.gprKeep 30#5 lm

theorem gprKeep_line {k : BitVec 5} {fa : FnAsm} {lm : Std.HashMap Lbl Nat}
    (h : fa.gprKeep k lm = true) {j : Nat} {x : Insn} {t : Option Clif.TrapCode}
    (hj : fa.lines.toList[j]? = some (.ins x t)) :
    x.gprKeep k ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = true := by
  have hlt : j < fa.lines.toList.length := by
    rcases Nat.lt_or_ge j fa.lines.toList.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  have := List.all_eq_true.mp h j (List.mem_range.mpr hlt)
  simpa only [hj] using this

end E2E
