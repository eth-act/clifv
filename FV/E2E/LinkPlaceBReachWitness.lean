import FV.E2E.LinkPlaceBReach
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.LinkArmPlaceBWitness

/-!
# Witnesses for `LinkPlaceBReach.lean`

* a placed state `sP` at `call fn0()` to the extern `e` (which keeps the memory): its step is
  call number `0`, its advance `advAt … 0 = 0` (`advAt_eq`), and the state after it is reached
  after one call with the counter advanced by `Σ_{j<1} advAt … j` (`nextAdv_reachN`);
* a placed state at a `jump` (no call): its step keeps the oracle (`step_bare_noCall_place`);
* on `LinkWitness`'s system `Ls`: `envOfB` advances the counter (`envAdv_envOfB`), the entry of
  `f` runs alone (`initState_linv_only`) and every state reached from it is placed with the
  advanced counter (`counter_reachN`).
-/

namespace E2E.LinkPlaceBReachWitness

open Backend Backend.Proof Clif InvokedNWitness CallPostExistsWitness LinkPlaceBWitness
open LinkArmPlaceBWitness

/-- `InvokedNWitness.sCall` with a placed memory (counter `0`). -/
def sP : State := { sCall with mem := mZ }

/-- The state after the call. -/
def sP1 : State := match step envE PE.bare sP with
  | .next s => s
  | _ => sP

theorem step_sP : step envE PE.bare sP = .next sP1 := rfl

theorem sP1_mem : sP1.mem = mZ := rfl

theorem callNum_sP : callNum sP = 1 := rfl

theorem linkFreeE : ∀ g ∈ PE.funcs, LinkFree g := by
  intro g hg b hb fn args he
  simp only [PE, List.mem_singleton] at hg
  subst hg
  simp only [fE, List.mem_singleton] at hb
  subst hb
  cases he

theorem linv_sP : LInv PE sP :=
  ⟨⟨by simp [sP, sCall, frE, PE], .inl ⟨blkE, by simp [sP, sCall, frE, fE],
    List.suffix_refl _, rfl⟩⟩, fun _ h => nomatch h⟩

theorem envAdv_E : EnvAdv envE := by
  intro n g hg vals m rvals m' hr
  unfold envE at hg
  dsimp only at hg
  split at hg
  · cases hg
    cases hr
    exact ⟨0, NextAdv.of_place rfl⟩
  · cases hg

/-- **`advAt_eq` applies**: the advance of call number `0` is `0`. -/
theorem advAt_sP : advAt envE PE.bare sP 0 = 0 :=
  advAt_eq .refl callNum_sP step_sP (NextAdv.of_place rfl) rfl rfl

/-- **`nextAdv_reachN` applies**: the state after one call is placed with the counter advanced
by `Σ_{j<1} advAt … j` (`= 0`). -/
theorem nextAdv_sP1 : ReachN envE PE.bare sP sP1 1 ∧
    NextAdv sP.mem sP1.mem (sumTo (advAt envE PE.bare sP) 1) ∧
    sumTo (advAt envE PE.bare sP) 1 = 0 := by
  have hr : ReachN envE PE.bare sP sP1 1 := by
    have := ReachN.snoc (ReachN.refl (env := envE) (p := PE.bare) (cs := sP)) step_sP
    rwa [callNum_sP] at this
  refine ⟨hr, (nextAdv_reachN linkFreeE envAdv_E linv_sP rfl rfl rfl hr).2.2, ?_⟩
  simp only [sumTo, advAt_sP]

/-! ## A step without a call -/

def blkJ0 : Block := { id := 0, term := .jump { block := 1 } }
def blkJ1 : Block := { id := 1, term := .ret [] }

def fJ : Function := { name := "fJ", sig := default, blocks := [blkJ0, blkJ1] }

def PJ : Program := { funcs := [fJ] }

def sJ : State :=
  { frame := { func := fJ, regs := Regs.empty, slots := [], body := [], term := blkJ0.term }
    callers := [], mem := mZ }

def sJ1 : State := match step Env.empty PJ.bare sJ with
  | .next s => s
  | _ => sJ

theorem step_sJ : step Env.empty PJ.bare sJ = .next sJ1 := rfl

theorem linv_sJ : LInv PJ sJ :=
  ⟨⟨by simp [sJ, PJ], .inr ⟨rfl, _, rfl⟩⟩, fun _ h => nomatch h⟩

theorem linkFreeJ : ∀ g ∈ PJ.funcs, LinkFree g := by
  intro g hg b hb fn args he
  simp only [PJ, List.mem_singleton] at hg
  subst hg
  simp only [fJ, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> cases he

/-- **`step_bare_noCall_place` applies**: the `jump` keeps the oracle. -/
theorem noCall_sJ : sJ1.mem.place = sJ.mem.place :=
  step_bare_noCall_place linkFreeJ linv_sJ rfl rfl step_sJ

/-! ## `LinkWitness`'s system -/

open LinkWitness LinkArmProphThmWitness InitB

/-- **`envAdv_envOfB` applies** at every depth. -/
theorem envAdv_envOfB_Ls (M : Nat) (g : Clif.Function) (c : BitVec 64) :
    EnvAdv (Ls.envOfB M g c) :=
  Ls.envAdv_envOfB (crun_adv_Ls M) g c

/-- **`initState_linv_only` and `counter_reachN` apply**: `f`'s entry from `memB` runs `f` alone
and every state its run reaches after `k` calls is placed at `f`'s `sp` with the counter
advanced by `Σ_{j<k} advAt … j`. -/
theorem counter_f : ∃ cs, initB = .ok cs ∧ LInv (Ls.P.only fF) cs ∧ cs.callers = [] ∧
    ∀ M s k, ReachN (linkEnvR Ls.P Ls.base (Ls.crun M)) Ls.P.bare cs s k →
      Ls.PlaceAtB s.mem (sp0 - BitVec.ofNat 64 (frameDrop (Ls.A fF).af))
        ((if fF.slots.isEmpty then ini0 else ini0.adv 1).adv
          (sumTo (advAt (linkEnvR Ls.P Ls.base (Ls.crun M)) Ls.P.bare cs) k)) := by
  obtain ⟨cs, hi, hpl, -⟩ := initState_memB_f (Img LinkWitness.P A)
  have hpf : Ls.P.func? fF.name = some fF := entryFacts.2.2.2.1
  obtain ⟨hI, hc⟩ := initState_linv_only hpf hi
  refine ⟨cs, hi, hI, hc, fun M s k hs => ?_⟩
  exact Ls.counter_reachN (crun_adv_Ls M) (Ls_ok.free fF (Clif.Program.func?_some hpf).1) hI hc
    hpl hs

end E2E.LinkPlaceBReachWitness
