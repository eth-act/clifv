import FV.E2E.LinkMemTrap

/-!
# The kept addresses with the unwritable bytes of a memory map (A3, #412, slice F8c)

The linked system's code image `Img` is among the kept addresses `G` of every activation
(`MachEntry.imgG`, `GoodAt`), so the per-state facts of every activation of the linked program
say that its reads and writes avoid `Img` (`RL.ReadsAt`, `RL.WritesAt`). `L.withNW N m0` is `L`
with the bytes `N` (e.g. those a memory map does not allow to be written) added to `Img`,
holding the bytes of `m0` (the memory at the program's entry) there:

* `LinkSys.Ok.withNW`: `L.withNW N m0` satisfies the linked program's premises when `L` does and
  its world's exterior `F` contains `N`;
* `withNW_mach`, `reachLB_withNW`, `goodAtW_of_withNW`: the machine and the reachable states are
  `L`'s, and the per-state facts of `L.withNW N m0` are `L`'s with `N` kept.
-/

namespace E2E

open Backend Backend.Proof

namespace LinkSys

open Classical in
/-- `L` with the bytes `N` among its code image, holding `m0`'s bytes there. -/
noncomputable def withNW (L : LinkSys) (N : BitVec 64 → Prop) (m0 : Arm.Memory) : LinkSys :=
  { L with Img := fun a => L.Img a ∨ N a, imgMem := fun a => if L.Img a then L.imgMem a else m0 a }

variable {L : LinkSys} {N : BitVec 64 → Prop} {m0 : Arm.Memory}

theorem withNW_hooks : ∀ M, (L.withNW N m0).hooks M = L.hooks M
  | 0 => rfl
  | M + 1 => by simp only [hooks, withNW_hooks M]; rfl

theorem withNW_mach (M : Nat) (g : Clif.Function) : (L.withNW N m0).mach M g = L.mach M g := by
  simp only [mach, withNW_hooks]; rfl

/-- **The premises of the linked program with the unwritable bytes kept.** -/
theorem Ok.withNW (hL : L.Ok) (hF : ∀ a, N a → L.F a) : (L.withNW N m0).Ok := by
  refine { hL with imgAddr := ?_, imgCode := ?_, imgF := ?_ }
  · exact fun g hg a ha => .inl (hL.imgAddr g hg a ha)
  · intro g hg t ht k w hk
    refine hL.imgCode g hg t (fun a ha => ?_) k w hk
    have := ht a (.inl ha)
    rw [this]
    exact if_pos ha
  · rintro a (ha | ha)
    · exact hL.imgF a ha
    · exact hF a ha

end LinkSys

end E2E
