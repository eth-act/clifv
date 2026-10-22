import FV.Concurrency.IselVary
import FV.Concurrency.VCodeThread

/-!
# A byte outside every event of a run is untouched (T2h, #311, layer 2d footprint)

`IselVary.store_touched`/`load_touched` show that no byte of a CLIF access is `Untouched` by the
statement's code. This file supplies the other half: a byte that lies outside every memory event
of the run (each instruction stepping with a precise footprint `IFoot`) *is* `Untouched`
(**`untouched_of_runOut`**). Together: every byte of the CLIF access lies in some event of the
run (**`store_in_events`**, **`load_in_events`**).

The per-instruction argument (`ifoot_out`): changing a byte that no event reads or writes keeps
the events' agreement (`sagrees_out`) and commutes with their writes (`applyW_out`), so by the
footprint the step has the same outcome with the byte changed after it as well.
-/

namespace Concurrency.IselFoot

open Arm ArmFoot ArmThread VCodeThread Backend Backend.Proof IselVary

/-- The byte `x` lies outside every event of `evs`. -/
def Out (x : BitVec 64) (evs : List Ev) : Prop :=
  ∀ e ∈ evs, ∀ k < e.n, e.addr + BitVec.ofNat 64 k ≠ x

theorem out_cons {x : BitVec 64} {e : Ev} {es : List Ev} (h : Out x (e :: es)) :
    (∀ k < e.n, e.addr + BitVec.ofNat 64 k ≠ x) ∧ Out x es :=
  ⟨h e (List.mem_cons_self ..), fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem write_store_comm {a x : BitVec 64} (h : a ≠ x) (b y : BitVec 8) (m : Memory) :
    write_store a b (write_store x y m) = write_store x y (write_store a b m) := by
  funext z
  simp only [write_store]
  by_cases hz : z = a
  · subst hz; simp [h]
  · simp [hz]

theorem succ_ne {a x : BitVec 64} {n : Nat} (h : ∀ k < n + 1, a + BitVec.ofNat 64 k ≠ x) :
    ∀ k < n, a + 1#64 + BitVec.ofNat 64 k ≠ x := by
  intro k hk e
  apply h (k + 1) (by omega)
  rw [← e, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]
  omega

theorem writeM_out : ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (m : Memory)
    (x : BitVec 64) (y : BitVec 8), (∀ k < n, a + BitVec.ofNat 64 k ≠ x) →
    ArmFoot.writeM n a v (write_store x y m) = write_store x y (ArmFoot.writeM n a v m)
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, a, v, m, x, y, h => by
    simp only [ArmFoot.writeM]
    have hx : a ≠ x := fun e => h 0 (by omega) (by simpa using e)
    rw [write_store_comm hx, writeM_out n _ _ _ x y (succ_ne h)]

theorem readM_out : ∀ (n : Nat) (a : BitVec 64) (m : Memory) (x : BitVec 64) (y : BitVec 8),
    (∀ k < n, a + BitVec.ofNat 64 k ≠ x) → readM n a (write_store x y m) = readM n a m
  | 0, _, _, _, _, _ => rfl
  | n + 1, a, m, x, y, h => by
    simp only [readM]
    have hx : a ≠ x := fun e => h 0 (by omega) (by simpa using e)
    rw [readM_out n _ _ x y (succ_ne h)]
    simp [read_store, write_store, hx]

theorem write1_out {e : Ev} {x : BitVec 64} (h : ∀ k < e.n, e.addr + BitVec.ofNat 64 k ≠ x)
    (y : BitVec 8) (m : Memory) : write1 (write_store x y m) e = write_store x y (write1 m e) := by
  simp only [write1]
  split
  · exact writeM_out _ _ _ _ _ _ h
  · rfl

/-- Changing a byte outside the events keeps their agreement. -/
theorem sagrees_out : ∀ {evs : List Ev} {m : Memory} {x : BitVec 64} (y : BitVec 8),
    Out x evs → SAgrees m evs → SAgrees (write_store x y m) evs
  | [], _, _, _, _, _ => trivial
  | e :: es, m, x, y, ho, ⟨hr, hs⟩ => by
    obtain ⟨he, hes⟩ := out_cons ho
    refine ⟨fun hd => ?_, ?_⟩
    · rw [readM_out _ _ _ _ _ he]; exact hr hd
    · rw [write1_out he]; exact sagrees_out y hes hs

/-- Changing a byte outside the events commutes with their writes. -/
theorem applyW_out : ∀ {evs : List Ev} {x : BitVec 64} (y : BitVec 8) (m : Memory),
    Out x evs → applyW evs (write_store x y m) = write_store x y (applyW evs m)
  | [], _, _, _, _ => rfl
  | e :: es, x, y, m, ho => by
    obtain ⟨he, hes⟩ := out_cons ho
    simp only [applyW]
    have : (if e.k.dir = .W then ArmFoot.writeM e.n e.addr e.val (write_store x y m) else
        write_store x y m) = write_store x y (if e.k.dir = .W then ArmFoot.writeM e.n e.addr e.val m else m) := by
      split
      · exact writeM_out _ _ _ _ _ _ he
      · rfl
    rw [this, applyW_out y _ hes]

theorem write_mem_bytes_one (x : BitVec 64) (y : BitVec (1 * 8)) (w : ArmState) :
    write_mem_bytes 1 x y w = setMem (write_store x (BitVec.extractLsb' 0 8 y) w.mem) w := by
  rw [write_mem_bytes_eq]
  rfl

/-- **One step with a precise footprint leaves a byte outside its events untouched**: from the
world with the byte changed, the step has the same outcome with the byte changed after it. -/
theorem ifoot_out {sem : Sem} {i : MInst} {uses : List CV} {w : ArmState} {evs : List Ev}
    {x : BitVec 64} (hf : IFoot sem i uses w evs) (ho : Out x evs) {outs : List CV}
    {w' : ArmState} {ctl : Ctl} (hs : sem i uses w = some (outs, w', ctl)) (y : BitVec (1 * 8)) :
    sem i uses (write_mem_bytes 1 x y w) = some (outs, write_mem_bytes 1 x y w', ctl) := by
  have h0 := hf.2 w.mem hf.1
  rw [setMem_self, hs] at h0
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0
  have hw' : w'.mem = applyW evs w.mem := by rw [h0.2.1]; rfl
  rw [write_mem_bytes_one, hf.2 _ (sagrees_out _ ho hf.1), hs, write_mem_bytes_one, hw',
    applyW_out _ _ ho]
  rfl

/-- **The run of `ms` from `ρ, w` keeps the byte `x` outside its events**: every instruction
reached steps with a precise footprint `evs` (`IFoot`) and `x` lies outside `evs`. -/
def RunOut (sem : Sem) (x : BitVec 64) : List MInst → (Nat → CV) → ArmState → Prop
  | [], _, _ => True
  | i :: ms, ρ, w => ∀ ops, i.operands = .ok ops →
      ∃ evs, IFoot sem i (vuses ops ρ) w evs ∧ Out x evs ∧
        ∀ outs w', sem i (vuses ops ρ) w = some (outs, w', .next) →
          RunOut sem x ms (vdefUpd ops outs ρ) w'

theorem succ_fall {e : SeqEnd CV ArmState} {ρ : Nat → CV} {w : ArmState}
    (h : e.succ = .fall ρ w) : e = .fall ρ w := by
  cases e <;> simp_all [SeqEnd.succ]

/-- **The footprint lemma**: a byte outside every event of the run is `Untouched` by it. -/
theorem untouched_of_runOut {sem : Sem} {x : BitVec 64} :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState}, RunOut sem x ms ρ w →
      Untouched sem ms ρ w x
  | [], ρ, w, _ => by
    intro ρ' w' h y
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | i :: ms, ρ, w, hr => by
    intro ρ' w' h y
    simp only [seqRun] at h ⊢
    split at h
    · exact absurd h (by simp)
    · rename_i ops hops
      obtain ⟨evs, hf, ho, hnext⟩ := hr ops hops
      split at h
      · exact absurd h (by simp)
      · rename_i outs w1 ctl hs
        rw [ifoot_out hf ho hs y]
        simp only
        split at h
        · rename_i hlen
          simp only [hlen, ↓reduceIte]
          split at h
          · obtain ⟨e, he, hee⟩ := Option.map_eq_some_iff.mp h
            have he' := succ_fall hee
            subst he'
            rw [untouched_of_runOut (hnext outs w1 hs) _ _ he y]
            rfl
          · simp at h
        · simp at h

/-- **Every byte of a store's access lies in an event of its code's run** (`store_touched` and the
footprint lemma). -/
theorem store_in_events {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)}
    {st' : LState} {ms : List MInst} {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {f : Clif.Function}
    (hok : LowerInstOk isem MR env p ctx inst results st rss st' ms)
    (hMR : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {big : Bool} {a n wd : Nat} {v : BitVec wd} (hval : cm.valid a n = true)
    (hout : ∀ c : Clif.Mem, c.allocs = cm.allocs →
      instOutcome env p fr c inst = .ok ([], c.writeBits big a n v))
    {k : Nat} (hk : k < n) : ¬ RunOut isem (BitVec.ofNat 64 (a + k)) ms ρ w := fun h =>
  store_touched hok hMR hf hv hd hmr hval hout hk (untouched_of_runOut h)

/-- **Every byte of a load's access lies in an event of its code's run** (`load_touched` and the
footprint lemma). -/
theorem load_in_events {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)}
    {st' : LState} {ms : List MInst} {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {f : Clif.Function}
    (hok : LowerInstOk isem MR env p ctx inst results st rss st' ms)
    (hMR : MemRelOk F sb syms f MR) (hres : results ≠ [])
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {a n : Nat} (hval : cm.valid a n = true)
    (hout : ∀ c : Clif.Mem, c.allocs = cm.allocs → (∀ j < n, (c.bytes (a + j)).isSome) →
      ∃ v vs c', instOutcome env p fr c inst = .ok (v :: vs, c'))
    (hinj : ∀ c1 c2 : Clif.Mem, ∀ v1 v2 vs1 vs2 c1' c2',
      instOutcome env p fr c1 inst = .ok (v1 :: vs1, c1') →
      instOutcome env p fr c2 inst = .ok (v2 :: vs2, c2') →
      v1.ty = v2.ty ∧ (v1 = v2 → ∀ j < n, c1.bytes (a + j) = c2.bytes (a + j)))
    (hinit : ∀ j < n, (cm.bytes (a + j)).isSome)
    {k : Nat} (hk : k < n) : ¬ RunOut isem (BitVec.ofNat 64 (a + k)) ms ρ w := fun h =>
  load_touched hok hMR hres hf hv hd hmr hval hout hinj hinit hk (untouched_of_runOut h)

end Concurrency.IselFoot
