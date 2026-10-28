import FV.E2E.LinkPlaceB

/-!
# Witnesses for the slot-byte counter on runs (`FV/E2E/LinkPlaceB.lean`)

The program `P` has one function `f` with an 8-byte slot that returns at once. From a memory
`m0` whose oracle has `sp = 0x8000`, `f`'s frame (drop 16, slot at offset 0) and the byte table
`0xAB` at counter `0`, the run of `f` returns with the counter at `1` (`run_next`), its activation
read the table's entry `1` into its slot (`entry_byte`), and the hypotheses of `runLoop_placeB`
and `linkEnvN_adv` hold for it (`placeB_f`, `adv_f`: the general results give the advanced
oracle, here with `e = 1`).
-/

namespace E2E.LinkPlaceBWitness

open Clif

/-- `f`: one 8-byte slot, returns. -/
def f : Function :=
  { name := "f", sig := {}, slots := [(0, ⟨8, some 8⟩)], blocks := [{ id := 0, term := .ret [] }] }

def P : Program := { funcs := [f] }

/-- `f`'s frame: a 16-byte drop, the slot at `sp`. -/
def fr : String → Option (Nat × (SlotId → Nat)) := fun n => if n = "f" then some (16, fun _ => 0) else none

/-- The byte table: `0xAB` everywhere. -/
def ini0 : SlotInit := { bytes := fun _ _ => 0xAB#8 }

def m0 : Mem := { place := some ⟨[0x8000#64], fr, some ini0⟩ }

theorem linkFree : ∀ g ∈ P.funcs, LinkFree g := by
  intro g hg
  simp only [P, List.mem_singleton] at hg
  subst hg
  intro b hb fn args h
  simp only [f, List.mem_singleton] at hb
  subst hb
  cases h

/-- `f`'s entry (frame and memory). -/
def r0 : Frame × Mem :=
  match enterFunc f [] m0 with
  | .ok r => r
  | _ => ({ func := f, regs := Regs.empty, slots := [], body := [], term := .ret [] }, m0)

theorem enter_ok : enterFunc f [] m0 = .ok r0 := rfl

def s0 : State := { frame := r0.1, callers := [], mem := r0.2 }

theorem init_ok : initState P "f" [] m0 = .ok s0 := rfl

theorem linv_s0 : LInv P s0 :=
  ⟨LFrame.enterFunc (by simp [P]) enter_ok, fun _ h => nomatch h⟩

theorem keeps_empty : EnvKeepsPlace Env.empty := by
  intro n g h
  simp [Env.empty] at h

/-- The activation's slot (at `0x8000 - 16`) holds the table's entry `1`. -/
theorem entry_byte : s0.mem.bytes (0x8000 - 16) = some 0xAB#8 := by decide

theorem s0_next : s0.mem.place.map (·.init.map (·.next)) = some (some 1) := by decide

/-- The run returns with the counter at `1` (one placed activation with slots). -/
theorem run_next : (match runLoop Env.empty P 5 s0 with
    | .returned _ m => m.place.map (fun pl => (pl.sps, pl.init.map (·.next)))
    | _ => none) = some ([0x8000#64], some 1) := by decide

theorem placeB_f : PlaceInvB [0x8000#64] fr ini0 s0 := initState_placeB init_ok rfl rfl

/-- `runLoop_placeB` on the run (non-vacuous: its premises hold and the run returns). -/
theorem runLoop_placeB_f : ∃ vals mem e, runLoop Env.empty P 5 s0 = .returned vals mem ∧
    mem.place = some ⟨[0x8000#64], fr, some (ini0.adv e)⟩ := by
  cases h : runLoop Env.empty P 5 s0 with
  | returned vals mem =>
    obtain ⟨e, he⟩ := runLoop_placeB linkFree (envAdv_of_keepsPlace keeps_empty)
      5 s0 vals mem linv_s0 placeB_f h
    exact ⟨vals, mem, e, rfl, he⟩
  | _ => have := run_next; rw [h] at this; cases this

/-- The linked environment advances the counter (base externs: none). -/
theorem adv_f : EnvAdv (linkEnvN P Env.empty 5) :=
  linkEnvN_adv linkFree (envAdv_of_keepsPlace keeps_empty)
