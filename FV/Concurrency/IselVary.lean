module

public import FV.Backend.Proof.IselMemSem

@[expose] public section

/-!
# The accesses of a lowered statement, by variation (T2h, #311, layer 2d core)

M4's per-statement contract `LowerInstOk` relates the CLIF outcome of a statement to the run
(`seqRun`) of its emitted code. It does not name the addresses the code accesses (finding 3 of
`docs/plans/atomics.md` §3e). They follow from it by *variation*. Change one byte of the CLIF
access on both sides: `MemRelOk.store` keeps the memory relation. If the code's run neither
reads nor writes that byte (`Untouched`: the run from the changed world is the same run, with
the byte changed after it too), then:

* **`store_touched`**: for a statement that writes `v` at `[a, a + n)` (a store), the relation
  after the step (`MemRelOk.bytes`) forces the byte to hold `v`'s byte both before and after
  the change, a contradiction;
* **`load_touched`**: for a statement whose first result is determined by the bytes it reads
  (a load, `atomic_load`/`atomic_rmw`/`atomic_cas`), the two runs leave the same register value
  (`ResultsHeld`) for two different results.

So every byte of the CLIF access is touched by the emitted code. With the footprint of the run
(the bytes a run touches are its events' bytes) and the segment's single memory event of the
access size, the event is the CLIF access.
-/

namespace Concurrency.IselVary

open Backend Backend.Proof

/-- **The byte at `x` is untouched by the run of `ms`**: from the world with `x` changed, the
run ends the same, with `x` changed after it. -/
def Untouched (isem : Sem) (ms : List MInst) (ρ : Nat → CV) (w : Arm.ArmState) (x : BitVec 64) :
    Prop :=
  ∀ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') → ∀ y : BitVec (1 * 8),
    seqRun isem ms ρ (Arm.write_mem_bytes 1 x y w) = some (.fall ρ' (Arm.write_mem_bytes 1 x y w'))

theorem read_write1 (x : BitVec 64) (y : BitVec (1 * 8)) (w : Arm.ArmState) :
    Arm.read_mem x (Arm.write_mem_bytes 1 x y w) = y := by
  simp [Arm.write_mem_bytes, Arm.write_mem, Arm.read_mem, Arm.read_store, Arm.write_store]

theorem writeBits1_bytes (c : Clif.Mem) (x : Nat) (y : BitVec 8) :
    (c.writeBits false x 1 y).bytes x = some y := by
  simp [Clif.Mem.writeBits, Clif.Mem.byteIndex]

theorem writeBits_allocs {w : Nat} (c : Clif.Mem) (big : Bool) (a n : Nat) (v : BitVec w) :
    (c.writeBits big a n v).allocs = c.allocs := rfl

theorem writeBits_valid {w : Nat} (c : Clif.Mem) (big : Bool) (a n : Nat) (v : BitVec w) (x k : Nat) :
    (c.writeBits big a n v).valid x k = c.valid x k := rfl

theorem writeBits_in {w : Nat} (c : Clif.Mem) (big : Bool) (a n : Nat) (v : BitVec w) {k : Nat}
    (hk : k < n) : (c.writeBits big a n v).bytes (a + k) =
      some (v.extractLsb' (8 * Clif.Mem.byteIndex big n k) 8) := by
  simp only [Clif.Mem.writeBits]
  rw [ite_eq_left_iff.mpr (fun h => absurd ⟨Nat.le_add_right a k, by omega⟩ h),
    Nat.add_sub_cancel_left]

theorem ne_succ (b : BitVec 8) : b + 1 ≠ b := by
  intro h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this
  omega

/-- **A store's bytes are touched by its code.** The statement writes `v` (big-endian or not) at
`[a, a + n)` on every memory with `cm`'s allocations (`hout`), the access is valid, and `MR` is
an M4 memory relation (`MemRelOk`): then no byte of `[a, a + n)` is `Untouched` by the code. -/
theorem store_touched {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState}
    {ms : List MInst} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function}
    (hok : LowerInstOk isem MR env p ctx inst results st rss st' ms)
    (hMR : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {big : Bool} {a n wd : Nat} {v : BitVec wd} (hval : cm.valid a n = true)
    (hout : ∀ c : Clif.Mem, c.allocs = cm.allocs →
      instOutcome env p fr c inst = .ok ([], c.writeBits big a n v))
    {k : Nat} (hk : k < n) : ¬ Untouched isem ms ρ w (BitVec.ofNat 64 (a + k)) := by
  intro hu
  have h0 := hok.run fr cm ρ w hf hv hd hmr
  rw [hout cm rfl] at h0
  obtain ⟨-, ρ', w', hrun, -, -⟩ := h0
  let vk : BitVec 8 := v.extractLsb' (8 * Clif.Mem.byteIndex big n k) 8
  let y : BitVec (1 * 8) := vk + 1
  let c2 := cm.writeBits false (a + k) 1 y
  have hmr2 : MR fr.slots c2 (Arm.write_mem_bytes 1 (BitVec.ofNat 64 (a + k)) y w) :=
    hMR.store _ _ _ _ _ _ hmr (valid_sub hval hk)
  have h1 := hok.run fr c2 _ (Arm.write_mem_bytes 1 (BitVec.ofNat 64 (a + k)) y w) hf hv hd hmr2
  rw [hout c2 rfl] at h1
  obtain ⟨-, ρ'', w'', hrun2, -, hmr3⟩ := h1
  rw [hu ρ' w' hrun y] at hrun2
  simp only [Option.some.injEq, SeqEnd.fall.injEq] at hrun2
  obtain ⟨-, rfl⟩ := hrun2
  have hb := hMR.bytes _ _ _ (a + k) vk hmr3
    (by rw [writeBits_valid, writeBits_valid]; exact valid_sub hval hk)
    (writeBits_in _ _ _ _ _ hk)
  rw [read_write1] at hb
  exact ne_succ vk hb

/-- **A load's bytes are touched by its code.** The statement has results (`results ≠ []`),
succeeds with a first result on every memory with `cm`'s allocations (`hout`), and its first
result determines the bytes of `[a, a + n)` it read (`hinj`); the access is valid and its bytes
initialised. Then no byte of `[a, a + n)` is `Untouched` by the code. -/
theorem load_touched {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState}
    {ms : List MInst} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function}
    (hok : LowerInstOk isem MR env p ctx inst results st rss st' ms)
    (hMR : MemRelOk F sb syms f MR) (hres : results ≠ [])
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {a n : Nat} (hval : cm.valid a n = true)
    (hout : ∀ c : Clif.Mem, c.allocs = cm.allocs → (∀ j < n, (c.bytes (a + j)).isSome) →
      ∃ v vs c', instOutcome env p fr c inst = .ok (v :: vs, c'))
    (hinj : ∀ c1 c2 : Clif.Mem, ∀ v1 v2 vs1 vs2 c1' c2',
      instOutcome env p fr c1 inst = .ok (v1 :: vs1, c1') →
      instOutcome env p fr c2 inst = .ok (v2 :: vs2, c2') →
      v1.ty = v2.ty ∧ (v1 = v2 → ∀ j < n, c1.bytes (a + j) = c2.bytes (a + j)))
    (hinit : ∀ j < n, (cm.bytes (a + j)).isSome)
    {k : Nat} (hk : k < n) : ¬ Untouched isem ms ρ w (BitVec.ofNat 64 (a + k)) := by
  intro hu
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp (hinit k hk)
  let y : BitVec (1 * 8) := b0 + 1
  let c2 := cm.writeBits false (a + k) 1 y
  have hinit2 : ∀ j < n, (c2.bytes (a + j)).isSome := by
    intro j hj
    simp only [c2, Clif.Mem.writeBits]
    split
    · rfl
    · exact hinit j hj
  obtain ⟨v1, vs1, c1', ho1⟩ := hout cm rfl hinit
  obtain ⟨v2, vs2, c2', ho2⟩ := hout c2 rfl hinit2
  have hmr2 : MR fr.slots c2 (Arm.write_mem_bytes 1 (BitVec.ofNat 64 (a + k)) y w) :=
    hMR.store _ _ _ _ _ _ hmr (valid_sub hval hk)
  have h0 := hok.run fr cm ρ w hf hv hd hmr
  rw [ho1] at h0
  obtain ⟨-, ρ', w', hrun, hrh, -⟩ := h0
  have h1 := hok.run fr c2 ρ _ hf hv hd hmr2
  rw [ho2] at h1
  obtain ⟨-, ρ'', w'', hrun2, hrh2, -⟩ := h1
  rw [hu ρ' w' hrun y] at hrun2
  simp only [Option.some.injEq, SeqEnd.fall.injEq] at hrun2
  obtain ⟨rfl, -⟩ := hrun2
  rcases hrh with h | ⟨hl1, hh1⟩
  · exact hres h
  rcases hrh2 with h | ⟨-, hh2⟩
  · exact hres h
  obtain ⟨rs, hrs⟩ : ∃ rs, rss[0]? = some rs :=
    ⟨rss[0]'(by rw [hl1]; simp), List.getElem?_eq_getElem _⟩
  obtain ⟨o1, cl1, e1, -, hv1⟩ := hh1 0 rs v1 hrs rfl
  obtain ⟨o2, cl2, e2, -, hv2⟩ := hh2 0 rs v2 hrs rfl
  rw [e1] at e2
  simp only [List.cons.injEq, Reg.vreg.injEq] at e2
  obtain ⟨⟨rfl, -⟩, -⟩ := e2
  obtain ⟨hty, hbytes⟩ := hinj cm c2 v1 v2 vs1 vs2 c1' c2' ho1 ho2
  have heq : v1 = v2 := by
    obtain ⟨t1, b1⟩ := v1
    obtain ⟨t2, b2⟩ := v2
    simp only at hty
    subst hty
    simp only [VHolds] at hv1 hv2
    rw [← hv1, ← hv2]
  have := hbytes heq k hk
  rw [hb0] at this
  simp only [c2, Clif.Mem.writeBits] at this
  rw [ite_eq_left_iff.mpr (fun h => absurd ⟨Nat.le_refl _, by omega⟩ h)] at this
  simp only [Nat.sub_self, Clif.Mem.byteIndex, Option.some.injEq] at this
  have e : b0 = b0 + 1 := by simpa [y] using this
  exact ne_succ b0 e.symm

end Concurrency.IselVary
