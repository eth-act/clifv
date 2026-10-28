import FV.E2E.LinkPlaceBTable
import FV.E2E.LinkSlotSysWitness

/-!
# Witness: a run depends on the slot-byte table only through the entries it uses

On the slotted system `Lsl` (`LinkSlotSysWitness`: `f` calls `h`, then `r`, which reads the bytes
`h` left in its slot), the whole-program run of `f` on `41` with the table `iniT` returns `82`
(`run_f`, two placed activations with slots). **`run_f_junk`**: with a table that agrees with
`iniT` on the entries `1` and `2` only (junk `7` everywhere else), `runWith_withTable` gives the
same run: it returns `82`.
-/

namespace E2E.LinkSlotSysWitness
open Clif LinkCheck

/-- `iniT` on the entries `1`, `2`; junk elsewhere. -/
def junkT : Nat → Nat → BitVec 8 := fun k a => if k = 1 ∨ k = 2 then iniT.bytes k a else 7#8

theorem envTable_base : EnvTable Lsl.base := by
  intro n g hg
  simp [Lsl, L0, LinkSys.std, LinkSys.withCrun, LinkSys.ofInput, ofRes, closedBase,
    Clif.Env.empty] at hg

theorem envAdv_base : EnvAdv Lsl.base := by
  intro n g hg
  simp [Lsl, L0, LinkSys.std, LinkSys.withCrun, LinkSys.ofInput, ofRes, closedBase,
    Clif.Env.empty] at hg

/-- **The run with the junk table returns `82`** (`runWith_withTable`: the table matters only at
the run's two entries). -/
theorem run_f_junk : ∃ cs v m, initState Lsl.P "f" [⟨.i64, 41#64⟩] (memS { bytes := junkT }) = .ok cs ∧
    Lsl.crun 100 cs = .returned [v] m ∧ v.bits.toNat = 82 := by
  obtain ⟨v, hr, hv, hp⟩ := run_f
  have hpl : (memS iniT).place = some ⟨[0x100000#64], Lsl.frames, some iniT⟩ := rfl
  obtain ⟨e, he⟩ := runLoop_placeB Lsl_ok.free envAdv_base 100 cs0 [v] (memOf iniT)
    (initState_linv init_ok) (initState_placeB init_ok hpl rfl) hr
  have he2 : e = 2 := by
    rw [he] at hp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, SlotInit.adv] at hp
    have := hp.2
    simp only [iniT] at this
    omega
  subst he2
  obtain ⟨hi, hr'⟩ := runWith_withTable (b := junkT) Lsl_ok.free envTable_base envAdv_base init_ok
    hpl rfl hr he fun x hx hx2 => by
      funext a
      simp only [junkT, show x = 1 ∨ x = 2 by simp only [iniT] at hx hx2; omega, ↓reduceIte]
  exact ⟨_, v, _, hi, hr', hv⟩

end E2E.LinkSlotSysWitness
