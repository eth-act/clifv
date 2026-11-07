import FV.E2E.RegLevelTryN

/-!
# `try_call` contracts at restricted states (SEM1 #537, step 2t)

`calleeTryP_at`, `calleeTryOkGP_of_call`: `calleeTry_at`/`calleeTryOkG_of_call` (`RegLevelTry.lean`)
from the plain call's contract at the states `Q` only (`CallSoundCtlGP Q`), giving
`CalleeTryOkGP Q`. Same proofs.
-/

namespace Backend.Proof

open Backend E2E

/-- **A `try_call`'s results from the plain call's contract**, at one state: where the plain
call's contract holds (`CallSoundCtlG`), the results the machine's callee leaves are the ones
`csem` gives (`csem` defines a `try_call` only when `X.call` returns at least `ti.rets`
results). -/
theorem calleeTryP_at {Q : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks}
    {ctx : FnCtx} {info : CallInfo} {ti : TryInfo} {gv : Nat → String → Prop}
    (hos : CallSoundCtlGP Q F K G s0 Pc (callExec H) (csemV gv F ctx X) (.call info) .next)
    (hPc : ∀ pc ic, Pc pc (.tryCall ic ti) → Pc pc (.call ic))
    (hcl : ti.clobberAll = false)
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    {s w : Arm.ArmState} {outs : List CV} {w' s' : Arm.ArmState} (hQ : Q s)
    (hK : K ≤ (spOf s).toNat) (hD : ∀ a, StackBelow K (spOf s) a → F a)
    (hG : ∀ a, G a → s.mem a = s0.mem a)
    (hops : (MInst.tryCall info ti).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok ())
    (hasg : (MInst.tryCall info ti).assign regs = .ok i') (hP : Pc (Arm.r .PC s) i')
    (hsw : SameWorld F s w) (hal : Arm.CheckSPAlignment s) (herr : Arm.r .ERR s = .None)
    (hsem : csemV gv F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length))
    (hex : callExec H i' s = some s') :
    ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2 := by
  intro p hp
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsem0 := csemV_sub hsem
  simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, ⟨hx, hr⟩, he⟩ := hsem0
  simp only [decide_eq_true_eq] at hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  have hsemC : csemV gv F ctx X (.call info) (useVals ops regs s) w =
      some (xo.take info.defs.length, w2, .next) := by
    have hg := csemV_guard_try hsem
    simp only [csemV, hg, ↓reduceIte]
    simp [csem, hx]
  obtain ⟨s1, hex1, -, -, hd, -, -⟩ := hos s hQ hK hD hG c wh ops regs (.call ic) w
    (xo.take info.defs.length) w2 (by rw [← operands_tryCall_call info ti]; exact hops)
    (by rw [← clobbers_tryCall hcl]; exact hst) hasg' (hPc _ _ hP) hsw hal herr hsemC
  have hs1 : s1 = s' := by
    simp only [callExec, hal, ↓reduceIte, Option.some.injEq] at hex hex1
    rw [← hex, ← hex1]
  subst hs1
  obtain ⟨a, b⟩ := p
  apply hd
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjn
    have e : (List.take info.defs.length
        (xo ++ List.map (fun _ => ofX 0) (List.drop xo.length info.defs)))[j]? =
        (xo.take info.defs.length)[j]? := by
      rw [List.getElem?_take, List.getElem?_take, List.getElem?_append_left (by omega)]
    rw [defRegs, List.getElem?_zip_eq_some, e] at hj
    exact List.mem_of_getElem? (by rw [defRegs, List.getElem?_zip_eq_some]; exact hj)
  · cases hj

/-- **`CalleeTryOkG` from the plain call's contract**: at `try_call` sites where the callee
contract of the plain call holds (`CallSoundCtlG`), the results the machine's callee leaves are
the ones `csem` gives. -/
theorem calleeTryOkGP_of_call {Q : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → TryInfo → Prop} {gv : Nat → String → Prop}
    (hos : ∀ ctx info ti, S info ti →
      CallSoundCtlGP Q F K G s0 Pc (callExec H) (csemV gv F ctx X) (.call info) .next)
    (hPc : ∀ pc ic ti, Pc pc (.tryCall ic ti) → Pc pc (.call ic))
    (hcl : ∀ info ti, S info ti → ti.clobberAll = false) :
    CalleeTryOkGP Q F K G s0 Pc X H S gv := by
  intro ctx info ti hS c wh ops regs i' s w outs w' s' hQ hK hD hG hops hst hasg hP hsw hal herr hsem
    hex
  exact calleeTryP_at (hos ctx info ti hS) (fun pc ic => hPc pc ic ti) (hcl info ti hS) hQ hK hD
    hG hops hst hasg hP hsw hal herr hsem hex

end Backend.Proof
