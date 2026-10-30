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

def RunOkABI {W : Type} (f : Clif.Function) (vc : VCode) (sem : ISem CV W)
    (MR : MemRelTW W) (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      ReturnABI f us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

theorem ReturnABI.ordinary {f : Clif.Function} {us : List (Reg × Reg)}
    (h : ReturnABI f us) (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    us.map (·.2) = (List.range us.length).map Reg.x := by
  unfold ReturnABI returnPins at h
  rw [ordinary] at h
  exact (retRegs_eq h).2

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
  exact ⟨uses,k,us,ops,ρ₁,w₁,outs,w₂,execution,pins.ordinary ordinary,arity,values,mem⟩

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

theorem RunOkABI.legacy {W : Type} {f : Clif.Function} {vc : VCode} {sem : ISem CV W}
    {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)} {vs : VState CV W} {o : Clif.Outcome}
    (h : RunOkABI f vc sem MR slots vs o)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) :
    RunOk vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w,cm0,ret,pins,rest⟩ := h
    exact ⟨us,outs,w,cm0,ret,pins.ordinary ordinary,rest⟩
  | _ => exact h
end Backend.Stock.Proof
