import FV.E2E.LinkArmPlaceB
import FV.E2E.SrcBoundedB
import FV.E2E.LinkPlaceBWitness
import FV.E2E.LinkArmProphThmWitness

/-!
# Witnesses for `LinkArmPlaceB.lean` and `SrcBoundedB.lean`

* `runsOf_nextAdv` on `LinkPlaceBWitness`'s run of `f` (counter `0 → 1`): `nextAdv_f`;
* `crun_advK`/`PlaceAtB.adv` on `LinkWitness`'s linked system `Ls` (base externs: none):
  `crun_adv_Ls`, `placeAtB_adv_Ls`;
* `bounded_placedB` on a one-function program `f0` with a placed empty slot, entered with the
  slot-byte oracle on (`bounded_f0`).
-/

namespace E2E.LinkArmPlaceBWitness

open Clif LinkPlaceBWitness

theorem keeps_empty : EnvKeepsPlace Env.empty := LinkPlaceBWitness.keeps_empty

/-- The run of `f` advances the counter (`runsOf_nextAdv`), by `1`. -/
theorem nextAdv_f : ∃ vals mem e, runLoop Env.empty P 5 s0 = .returned vals mem ∧
    NextAdv m0 mem e ∧ mem.place.map (fun pl => pl.init.map (·.next)) = some (some 1) := by
  obtain ⟨vals, mem, -, hr, -⟩ := runLoop_placeB_f
  obtain ⟨e, he⟩ := runsOf_nextAdv (runsOf_runLoop Env.empty P 5) linkFree
    (envAdv_of_keepsPlace keeps_empty) init_ok hr
  refine ⟨vals, mem, e, hr, he, ?_⟩
  have := run_next
  rw [hr] at this
  simp only [Option.map_some] at this ⊢
  cases hp : mem.place with
  | none => rw [hp] at this; cases this
  | some pl => rw [hp] at this; simp only [Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at this; exact congrArg some this.2

open LinkArmProphThmWitness in
/-- The linked system `Ls` advances the counter at every depth. -/
theorem crun_adv_Ls (M : Nat) : EnvAdv (linkEnvR Ls.P Ls.base (Ls.crun M)) :=
  Ls.crun_advK Ls_ok.free keeps_empty M

open LinkArmProphThmWitness in
/-- A memory placed at `0x8000` with the byte table `0xAB` stays placed with the counter
advanced (`e = 0` for an oracle-keeping step). -/
theorem placeAtB_adv_Ls :
    Ls.PlaceAtB ({ place := some ⟨[0x8000#64], Ls.frames, some ini0⟩ } : Mem) 0x8000#64 ini0 ∧
    Ls.PlaceAtB ({ place := some ⟨[0x8000#64], Ls.frames, some ini0⟩ } : Mem) 0x8000#64
      (ini0.adv 0) :=
  ⟨⟨[], rfl⟩, LinkSys.PlaceAtB.adv ⟨[], rfl⟩ (NextAdv.of_place rfl)⟩

/-! ## `bounded_placedB` -/

/-- `f0`: one empty placed slot, returns. -/
def f0 : Function :=
  { name := "f0", sig := {}, slots := [(0, ⟨0, some 8⟩)], blocks := [{ id := 0, term := .ret [] }] }

def P0 : Program := { funcs := [f0] }

/-- `f0`'s frame: no drop, the slot at `sp`. -/
def fr0 : String → Option (Nat × (SlotId → Nat)) := fun _ => some (0, fun _ => 0)

def mZ : Mem := { place := some ⟨[0x8000#64], fr0, some ini0⟩ }

def rZ : Frame × Mem :=
  match enterFunc f0 [] mZ with
  | .ok r => r
  | _ => ({ func := f0, regs := Regs.empty, slots := [], body := [], term := .ret [] }, mZ)

theorem enterZ_ok : enterFunc f0 [] mZ = .ok rZ := rfl

def sZ : State := { frame := rZ.1, callers := [], mem := rZ.2 }

/-- The entry advanced the counter to `1`. -/
theorem sZ_place : sZ.mem.place = some ⟨[0x8000#64, 0x8000#64], fr0, some { ini0 with next := 1 }⟩ :=
  rfl

theorem sZ_allocs : sZ.mem.allocs = [{ base := 0x8000, size := 0 }] := rfl

theorem linkFree0 : ∀ g ∈ P0.funcs, LinkFree g := by
  intro g hg
  simp only [P0, List.mem_singleton] at hg
  subst hg
  intro b hb fn args h
  simp only [f0, List.mem_singleton] at hb
  subst hb
  cases h

theorem linv_sZ : LInv P0 sZ :=
  ⟨LFrame.enterFunc (by simp [P0]) enterZ_ok, fun _ h => nomatch h⟩

theorem bounded_sZ : Opt.Legal.MemBounded sZ.mem := by
  intro a n hv
  simp only [Mem.valid, sZ_allocs, List.any_cons, List.any_nil, Bool.or_false, Alloc.contains,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  omega

/-- **`bounded_placedB` applies**: every state reachable from `f0`'s entry under no externs has
bounded memory (budget `0`; the slot is empty). -/
theorem bounded_f0 : ∀ s', Opt.Legal.SReach Env.empty P0 sZ s' → Opt.Legal.MemBounded s'.mem := by
  refine SrcBounded.bounded_placedB linkFree0 (envAdv_of_keepsPlace keeps_empty) ?_
    (fun _ _ => 0) (fun _ => True) fr0 linv_sZ bounded_sZ rfl sZ_place (Nat.zero_le _) trivial ?_
  · intro n g h
    simp [Env.empty] at h
  · intro t t1 _ hIt _ hs _ _
    have hmem := (step_next_linv linkFree0 hIt hs).1.1.1
    simp only [P0, List.mem_singleton] at hmem
    refine ⟨0, fun _ => 0, rfl, ?_, Nat.le_refl _, trivial⟩
    rw [hmem]
    intro p hp
    simp only [f0, List.mem_singleton] at hp
    subst hp
    exact Nat.le_refl _

end E2E.LinkArmPlaceBWitness
