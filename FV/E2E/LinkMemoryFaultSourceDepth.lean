import FV.E2E.LinkMemoryFaultSource

namespace E2E.MemoryFaultSource
open Clif
set_option autoImplicit false
set_option Elab.async false

/-- The original bounded-fuel source linker derives local mapping internally. -/
theorem runLoop_linkN_mapFaults {P : Program} {base : Env} {f : Function} {syms : String → Option Nat}
    (M : Nat) (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScope P base syms) {E : Env}
    (hEn : E.names = (linkEnvN P base M).names) (hEs : E.sigOf = (linkEnvN P base M).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvN P base M).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvN P base M).extern h.name)
    {mp : ArmFault.MemMap} :
    ∀ (N : Nat) (s : State), MapFaults mp base P s → N ≤ M + 1 → LInv P s → LInv (P.only f) s →
      (¬ IndFree f → s.mem.symbols = syms) →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop E P.bare m s = runLoop base P N s ∧ MapFaults mp E P.bare s := fun N s mapped hN hI hIf hsy hst hof =>
  runLoop_linkR_mapFaults (runLoop base P M) M s hnd hf hP hio hEn hEs hEb hEp
    (fun t0 _ n _ _ hn _ hof' => by
      have := runLoop_add base P n t0 hof' (M - n)
      rwa [Nat.add_sub_cancel' hn] at this)
    mapped N s hN (.refl s) hI hIf hsy hst hof


/-- The original depth-bounded source linker derives local mapping internally. -/
theorem runLoop_linkD_mapFaults {P : Program} {base : Env} {f : Function} {syms : String → Option Nat}
    (F d : Nat) (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScope P base syms) {E : Env}
    (hEn : E.names = (linkEnvD P base F d).names) (hEs : E.sigOf = (linkEnvD P base F d).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvD P base F d).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvD P base F d).extern h.name)
    (N : Nat) (s : State) (hN : N ≤ F + 1) (hd : DepthLe base P d s) (hI : LInv P s)
    (hIf : LInv (P.only f) s) (hsy : ¬ IndFree f → s.mem.symbols = syms)
    (hst : ∀ msg, runLoop base P N s ≠ .stuck msg) (hof : runLoop base P N s ≠ .outOfFuel)
    {mp : ArmFault.MemMap} (mapped : MapFaults mp base P s) :
    ∃ m, runLoop E P.bare m s = runLoop base P N s ∧ MapFaults mp E P.bare s :=
  runLoop_linkR_mapFaults (runD base P F d) F s hnd hf hP hio hEn hEs hEb hEp
    (fun t0 _ n hK hr hn _ hof' => by
      simp only [runD, hd.callee hK hr, and_self, ↓reduceIte]
      have := runLoop_add base P n t0 hof' (F - n)
      rwa [Nat.add_sub_cancel' hn] at this)
    mapped N s hN (.refl s) hI hIf hsy hst hof

end E2E.MemoryFaultSource
