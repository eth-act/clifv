import FV.Concurrency.ClifThreadI
import FV.Clif.Parse

/-!
# Witness: a call into a callee with a stack slot under `CStepI` (#473, (iv))

`%f(v0) { v1 = call fn0(v0); return v1 }` calling `%g`, which has an 8-byte `explicit_slot`,
with the slot-placement oracle placing `%g`'s frame `0xF0` bytes below `sp = 0x7000` and its
slot at offset `0x10`:

* `cstepI_callW`: the call is a `CStepI` from the empty mask (`cstepI_call`), and the mask after
  it contains the slot's bytes (`maskW`): a later read of them is stuck until `%g` writes them;
* `ownW`: `cstepI_own` on it — the step is `Clif.step` on the caller's own memory;
* `not_cstepW`: no `CStep` enters `%g` (`allocAt` clears the slot's bytes, which an event-free
  `CStep` must keep on every byte memory) — the gap `CStepI` closes;
* `emptyW`, `emptyW'`: with the bump allocator (`memB`) no byte is placed, the mask stays empty,
  and `cstepI_empty` gives the old `CStep`.
-/

namespace Concurrency.ClifThreadI.Witness

open Prog ClifThread

def srcW : String := "
function %g(i64) -> i64 {
    ss0 = explicit_slot 8
block0(v0: i64):
    return v0
}

function %f(i64) -> i64 {
    fn0 = colocated %g(i64) -> i64
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def pW : Clif.Program := match Clif.parse srcW with
  | .ok p => p
  | .error _ => default

def gW : Clif.Function := pW.funcs.headD default
def fW : Clif.Function := (pW.funcs.drop 1).headD default
def B0W : Clif.Block := fW.blocks.headD default

/-- The slot oracle: `%g`'s frame drop `0xF0`, its slot at offset `0x10`. -/
def placeW : Clif.Place := ⟨[0x7000#64], fun n => if n = "g" then some (0xF0, fun _ => 0x10) else none, none⟩

/-- The caller's memory: nothing allocated, the slot oracle. -/
def memW : Clif.Mem := { place := some placeW }

/-- The caller's memory with the bump allocator. -/
def memB : Clif.Mem := {}

def regsW : Clif.Regs := (Clif.Regs.empty.setMany (B0W.params.map (·.1)) [⟨.i64, 0⟩]).getD Clif.Regs.empty

def csW (m : Clif.Mem) : Clif.State :=
  { frame := { func := fW, regs := regsW, slots := [], body := B0W.body, term := B0W.term }
    callers := []
    mem := m }

def envW : Clif.Env := default

def isNext : Clif.StepResult → Bool
  | .next _ => true
  | _ => false

theorem factsW : B0W.body = [{ results := [1], inst := .call 0 [0] }] ∧
    fW.extern? 0 = some ((fW.extern? 0).getD default) ∧
    pW.func? ((fW.extern? 0).getD default).name = some gW ∧
    gW.slots = [(0, { size := 8 })] ∧ gW.name = "g" ∧
    isNext (Clif.step envW pW (csW memW)) = true ∧ isNext (Clif.step envW pW (csW memB)) = true := by
  native_decide

/-- The state after the call (the oracle's placement). -/
def sW (m : Clif.Mem) : Clif.State := match Clif.step envW pW (csW m) with
  | .next s => s
  | _ => csW m

theorem stepW (m : Clif.Mem) (h : isNext (Clif.step envW pW (csW m)) = true) :
    Clif.step envW pW (csW m) = .next (sW m) := by
  unfold sW
  revert h
  cases Clif.step envW pW (csW m) <;> simp [isNext]

/-- **The call enters `%g` under `CStepI`, masking its slot.** -/
theorem cstepI_callW :
    CStepI envW pW (.run (csW memW), fun _ => False) []
      (.run (sW memW), fun a => False ∨ slotZ gW memW a) := by
  obtain ⟨hb, he, hc, -, -, hn, -⟩ := factsW
  exact cstepI_call (s := csW memW) hb he hc (stepW memW hn) _ (fun pl h => by cases h; rfl)

/-- The mask after the call contains the slot's 8 bytes at `0x7000 - 0xF0 + 0x10`. -/
theorem maskW : ∀ k < 8, slotZ gW memW (0x6F20 + k) := by
  obtain ⟨-, -, -, hsl, hn, -⟩ := factsW
  intro k hk
  unfold slotZ
  simp only [memW, placeW, hn, ite_true, List.headD_cons]
  rw [hsl]
  refine ⟨(0, { size := 8 }), List.mem_singleton_self _, ?_⟩
  have e : (0x7000#64 - BitVec.ofNat 64 0xF0).toNat = 0x6F10 := by decide
  simp only [e]
  omega

/-- `cstepI_own` on the call: it is `Clif.step` on the caller's own memory. -/
theorem ownW : ∃ t'', res (Clif.step envW pW (csW memW)) =
    some (t'', mix (fun a => False ∨ slotZ gW memW a) (applyEvs bytesI (csW memW).mem.bytes ([] : List (Ev SKind BVal)))) :=
  let ⟨t'', h, _⟩ := cstepI_own cstepI_callW (fun _ h => h.elim) trivial
  ⟨t'', h⟩

/-- **No `CStep` enters `%g`**: the call clears the slot's bytes. -/
theorem not_cstepW (t' : TState) : ¬ CStep envW pW (.run (csW memW)) [] t' := by
  rintro ⟨-, -, hf⟩
  obtain ⟨t'', hr, -⟩ := hf (fun _ => some 0) trivial
  obtain ⟨-, -, -, -, -, hn, -⟩ := factsW
  have hB := (cstepI_callW.2.2.2 (fun _ => some 0) trivial)
  obtain ⟨t3, hr3, -⟩ := hB
  have e : withBytes (csW memW) (mix (fun _ => False) fun _ => some 0) =
      withBytes (csW memW) (fun _ => some 0) := by rw [mix_false]
  rw [e, hr] at hr3
  simp only [Option.some.injEq, Prod.mk.injEq] at hr3
  have := congrFun hr3.2 0x6F20
  simp only [applyEvs, List.foldl_nil, mix] at this
  rw [if_pos (.inr (by simpa using maskW 0 (by decide)))] at this
  cases this

/-- With the bump allocator the call is a `CStep`, and `cstepI_empty` turns it into a `CStepI`
with the empty masks. -/
theorem emptyW : CStepI envW pW (.run (csW memB), fun _ => False) [] (.run (sW memB), fun _ => False) := by
  obtain ⟨hb, he, hc, -, -, -, hn⟩ := factsW
  have h := cstepI_call (s := csW memB) hb he hc (stepW memB hn) (fun _ => False)
    (fun pl h => by cases h)
  have e : (fun a => False ∨ slotZ gW (csW memB).mem a) = fun _ => False := by
    funext a; simp [slotZ, csW, memB]
  rw [e] at h
  exact h

theorem emptyW' : CStep envW pW (.run (csW memB)) [] (.run (sW memB)) := cstepI_empty.mp emptyW

end Concurrency.ClifThreadI.Witness
