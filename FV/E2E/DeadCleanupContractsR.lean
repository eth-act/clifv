import FV.E2E.DeadCleanupContracts
import FV.E2E.RegLevelDriverSemR

/-!
# The value semantics' call contracts with registers (#753, stage R2)

`DeadCleanupContracts`' contracts for `valueSem` give the contracts with registers for
`regG P (valueSem …)` at the trivial pin: `callsRefinePR_valueSem`, `indCallsRefinePR_valueSem`.
-/

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

/-- A GOT load of `valueSem` gives the symbol's link-time address. -/
theorem valueSem_gotR {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} :
    ∀ (rd : Reg) (n : String) (w : Arm.ArmState) (r : List CV × Arm.ArmState × Ctl),
      valueSem F ctx X (.loadExtNameGot rd n) [] w = some r → r.1 = [ofX (X.sym n 0)] := by
  intro rd n w r h
  simp only [valueSem, specForm, pureForm, cmpForm, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, csem, Option.some.injEq] at h
  rw [← h]

/-- **The callee contract with registers for the register-guarded `valueSem`.** -/
theorem callsRefinePR_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    {P : BitVec 64 → Clif.Signature → Prop}
    (hX : XCallsOk env exts MR X) (hP : RegCompatGot P exts (fun n => X.sym n 0)) :
    CallsRefinePR (fun _ _ _ _ => True) F env exts MR (regG P (valueSem F ctx X)) :=
  ((callsRefine_valueSem hX).toP _).regG valueSem_gotR hP

/-- **The indirect-call contract with registers for the register-guarded `valueSem`.** -/
theorem indCallsRefinePR_valueSem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat} {P : BitVec 64 → Clif.Signature → Prop}
    (hX : XCallsIndOk env sigs MR X) (hsym : ∀ n b, syms n = some b →
      X.sym n 0 = BitVec.ofNat 64 b)
    (hMR : ∀ sl cm w, MR sl cm w → cm.symbols = syms) (hP : RegCompatInd P env sigs syms) :
    IndCallsRefinePR (fun _ _ _ _ => True) env sigs MR (regG P (valueSem F ctx X)) :=
  ((indCallsRefine_valueSem (ctx := ctx) (F := F) hX hsym hMR).toP _).regG hMR hP

/-- `FlagsPend` of a semantics gives that of its register-guarded form. -/
theorem FlagsPend.regG {W : Type} {P : BitVec 64 → Clif.Signature → Prop} {sem : ISem CV W}
    {w wb : W} (h : FlagsPend sem w wb) : FlagsPend (regG P sem) w wb :=
  ⟨fun K us r hK hs => by
    obtain ⟨hg, hs'⟩ := regG_inv hs
    rw [regG_of hg]
    exact h.1 K us r hK hs',
   fun j us outs ctl hj hs => by
    obtain ⟨hg, hs'⟩ := regG_inv hs
    rw [regG_of hg]
    exact h.2 j us outs ctl hj hs'⟩

/-- `CmpOverwrite` of a semantics gives that of its register-guarded form. -/
theorem CmpOverwrite.regG {W : Type} {P : BitVec 64 → Clif.Signature → Prop} {sem : ISem CV W}
    (h : CmpOverwrite sem) : CmpOverwrite (regG P sem) :=
  ⟨fun i us w outs w' ctl hi hs =>
    let ⟨h1, h2⟩ := h.1 i us w outs w' ctl hi (regG_sub hs)
    ⟨h1, h2.regG⟩,
   fun l us w outs w' ctl hs => h.2 l us w outs w' ctl (regG_sub hs)⟩

end Backend.DeadCleanup
