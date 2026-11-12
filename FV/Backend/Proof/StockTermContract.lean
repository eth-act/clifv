import FV.Backend.Proof.IselCtlTerm
import FV.Backend.Proof.StockReturnABI
import FV.Backend.Proof.LowerSim

/-! ABI-aware terminator and whole-run contracts. The legacy contracts and
their callers are retained; ordinary returns can recover their old interface.
Implicit struct returns instead retain the actual x8 pin. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

def ReturnABI (f : Clif.Function) (us : List (Reg × Reg)) : Prop :=
  returnPins f us.length = some (us.map (·.2))

structure LowerTermOkABI {W : Type} (isem : ISem CV W) (MR : MemRelTW W) (ctx : Ctx)
    (t : Clif.Terminator) (targets : List Label) (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : W),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match t with
    | .ret xs => ∀ vals, fr.getMany xs = .ok vals → UsesOk st fr ms ∧
        ∃ k us ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k (.rets us) ops ρ₁ w₁ outs w₂ .ret) ∧
          ReturnABI ctx.func us ∧ us.length = vals.length ∧
          AllHold vals (vuses ops ρ₁) ∧ MR fr.slots cm w₂
    | .trap c => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧ trapCode? i = some c
    | t => (∀ i, ms.getLast? = some i → i.targets = targets) ∧ ∀ j, branchIdx fr t = .ok j →
        UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧ k + 1 = ms.length ∧
          MR fr.slots cm w₂

/-- `ReturnABI` with the number of returned registers: the CLIF return values, then the ABI
returns lowering appends (`sretRet`: an `sret` function's struct pointer). `RunOkABI` keeps the
count (#587) so that its pins are `RetPins` (`ReturnABIV.retPins`): an ordinary function returns
its values in x0, x1, … and nothing after them. -/
structure ReturnABIV (f : Clif.Function) (vals : List Clif.Val) (us : List (Reg × Reg)) : Prop where
  abi : ReturnABI f us
  count : us.length = vals.length + (sretRet f).length

def RunOkABI {W : Type} (f : Clif.Function) (vc : VCode) (sem : ISem CV W)
    (MR : MemRelTW W) (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      ReturnABIV f vals us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

theorem ReturnABI.ordinary {f : Clif.Function} {us : List (Reg × Reg)}
    (h : ReturnABI f us) (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    us.map (·.2) = (List.range us.length).map Reg.x := by
  unfold ReturnABI returnPins at h
  rw [ordinary] at h
  exact (retRegs_eq h).2

/-- Without an `sret` ABI return the function returns no implicit struct pointer. -/
theorem sretRet_nil_of_ordinary {f : Clif.Function}
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : sretRet f = [] := by
  have same : sigRets f.sig = f.sig.returns := by
    unfold sigRets at ordinary ⊢
    cases hp : f.sig.params.find? (·.purpose == .sret) with
    | none => rfl
    | some p =>
      simp only at ordinary ⊢
      by_cases he : f.sig.returns.isEmpty
      · have := List.find?_some hp
        simp_all
      · simp [he]
  unfold sretRet
  simp [same]

theorem ReturnABIV.ordinary {f : Clif.Function} {vals : List Clif.Val} {us : List (Reg × Reg)}
    (h : ReturnABIV f vals us) (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    us.map (·.2) = (List.range us.length).map Reg.x :=
  h.abi.ordinary ordinary

/-- The pins of an ordinary function's return are `RetPins`: x0, x1, … for its values. -/
theorem ReturnABIV.retPins {f : Clif.Function} {vals : List Clif.Val} {us : List (Reg × Reg)}
    (h : ReturnABIV f vals us) (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    RetPins vals us := by
  have hc := h.count
  rw [sretRet_nil_of_ordinary ordinary, List.length_nil, Nat.add_zero] at hc
  exact RetPins.of_ordinary (h.ordinary ordinary) (Nat.le_of_eq hc)

theorem LowerTermOkABI.legacy {W : Type} {isem : ISem CV W} {MR : MemRelTW W}
    {ctx : Ctx} {t : Clif.Terminator} {targets : List Label} {st st' : LState} {ms : List MInst}
    (h : LowerTermOkABI isem MR ctx t targets st st' ms)
    (ordinary : (sigRets ctx.func.sig).any (·.purpose == .sret) = false) :
    LowerTermOk isem MR ctx t targets st st' ms := by
  refine ⟨h.mono,h.defs,?_⟩
  intro fr cm ρ w func held consistent memory
  have run := h.run fr cm ρ w func held consistent memory
  cases t <;> try exact run
  rename_i xs
  intro vals read
  obtain ⟨uses,k,us,ops,ρ₁,w₁,outs,w₂,execution,pins,arity,values,mem⟩ := run vals read
  refine ⟨uses,k,us,ops,ρ₁,w₁,outs,w₂,execution,?_,arity,values,mem⟩
  rw [sretRet_nil_of_ordinary ordinary, List.length_nil, Nat.sub_zero, ← arity,
    map_retX_of_le (Nat.le_refl _)]
  exact pins.ordinary ordinary

theorem RunOkABI.prefix {W : Type} {f : Clif.Function} {vc : VCode} {sem : ISem CV W}
    {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)} {vs vs' : VState CV W} {o : Clif.Outcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOkABI f vc sem MR slots vs' o) :
    RunOkABI f vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w,cm0,ret,rest⟩ := h'
    exact ⟨us,outs,w,cm0,VRetFrom.prefix h ret,rest⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | _ => trivial

/-- The whole-run contract of `RunOk` before #587, with every return register pinned to
x0, x1, … (`RunOk` now pins the returns after the CLIF values, an implicit struct-return pointer,
to x8 as Cranelift does). `RunOkABI.legacy` concludes this exact old meaning. -/
def RunOkX {W : Type} (vc : VCode) (sem : ISem CV W) (MR : MemRelTW W)
    (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

theorem RunOkABI.legacy {W : Type} {f : Clif.Function} {vc : VCode} {sem : ISem CV W}
    {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)} {vs : VState CV W} {o : Clif.Outcome}
    (h : RunOkABI f vc sem MR slots vs o)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    RunOkX vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w,cm0,ret,pins,rest⟩ := h
    exact ⟨us,outs,w,cm0,ret,pins.ordinary ordinary,rest⟩
  | _ => exact h
end Backend.Stock.Proof
