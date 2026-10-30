import FV.Concurrency.IselThread

/-!
# The segment of a memory statement (T2h, #311, layer 2e): auxiliary facts

* `filter_eq_singleton`: a list whose filter is one element splits around it;
* `mem_facts`: one successful run of a memory statement gives its outcome on other memories
  (`IselClif.StoreFacts`/`LoadFacts`), per kind (the dispatch of `IselClif.access_in_events`);
* `corr_one`: one source step against a target segment with one step with events.
-/

namespace Concurrency.IselMem

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm IselThread IselClif Code
  ClifCStep ArmFoot

theorem filter_eq_singleton {α : Type} {p : α → Bool} :
    ∀ {l : List α} {x : α}, l.filter p = [x] →
      ∃ l1 l2, l = l1 ++ x :: l2 ∧ (∀ y ∈ l1, p y = false) ∧ (∀ y ∈ l2, p y = false) ∧ p x = true
  | [], _, h => by simp at h
  | y :: l, x, h => by
    by_cases hy : p y = true
    · rw [List.filter_cons_of_pos hy] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      refine ⟨[], l, rfl, by simp, fun z hz => ?_, hy⟩
      have : z ∉ l.filter p := by rw [h2]; simp
      simpa [List.mem_filter, hz] using this
    · rw [List.filter_cons_of_neg hy] at h
      obtain ⟨l1, l2, rfl, h1, h2, h3⟩ := filter_eq_singleton h
      refine ⟨y :: l1, l2, rfl, fun z hz => ?_, h2, h3⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · simpa using hy
      · exact h1 z hz

/-- **The facts of a memory statement from one successful run** (the dispatch of
`IselClif.access_in_events`). -/
theorem mem_facts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {inst : Clif.Inst} {vs : List Clif.Val} {cm' : Clif.Mem}
    (h : instOutcome env p fr cm inst = .ok (vs, cm')) {a n : Nat}
    (hacc : access fr inst = some (a, n)) (hro : isCas inst = true → cm.readonlyAt a n = false) :
    (isStore inst = true → StoreFacts env p fr cm inst a n) ∧
      (isStore inst = false → LoadFacts env p fr cm inst a n) := by
  cases inst <;> simp only [access, reduceCtorEq] at hacc
  case load op ty fl pp off =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun h => by simp [isStore] at h, fun _ => load_facts hle h hpv⟩
  case store op ty fl x pp off =>
    obtain ⟨pv, hpv, he⟩ := access_some hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun _ => store_facts h hpv, fun h => by simp [isStore] at h⟩
  case atomicRmw op ty fl pp x =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun h => by simp [isStore] at h, fun _ => atomicRmw_facts hle h hpv⟩
  case atomicCas ty fl pp ex x =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun h => by simp [isStore] at h, fun _ => atomicCas_facts hle h hpv (hro rfl)⟩
  case atomicLoad ty fl pp =>
    obtain ⟨hle, pv, hpv, he⟩ := access_some_ite hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun h => by simp [isStore] at h, fun _ => atomicLoad_facts hle h hpv⟩
  case atomicStore ty fl x pp =>
    obtain ⟨pv, hpv, he⟩ := access_some hacc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun _ => atomicStore_facts h hpv, fun h => by simp [isStore] at h⟩

/-- **One source step against a target segment with one step with events.** -/
theorem corr_one {x : List (Prog.Ev SKind BVal)} {pre post : List (List Ev)} {y : List Ev}
    (hpre : ∀ e ∈ pre, e = []) (hpost : ∀ e ∈ post, e = [])
    (hxy : PW (EvRel Maps) x (y.map ProgE2E.convEv)) (hx : x ≠ []) :
    Corr Maps [x] (conv (pre ++ y :: post)) := by
  rw [conv_append]
  have h1 := corr_nil_tgts (trT := pre) hpre
  have h2 : Corr Maps [x] (conv (y :: post)) := .both hxy hx (corr_nil_tgts hpost)
  simpa using h1.append h2

/-! ## CLIF side -/

theorem cstep_withBytes {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {B : Bytes}
    {evs : List (Prog.Ev SKind BVal)} {t : TState} :
    CStep env p (.run (withBytes s B)) evs t ↔ CStep env p (.run s) evs t := Iff.rfl

/-- **A thread whose step fails on every byte memory has no step.** -/
theorem done_of_all {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (h : ∀ B, res (Clif.step env p (withBytes s B)) = none) : Done env p (.run s) := by
  rintro ⟨evs, t', ⟨-, ⟨B, hB⟩, hf⟩⟩
  obtain ⟨t'', h1, -⟩ := hf B hB
  rw [h B] at h1; cases h1

theorem withBytes_writeBits (s : Clif.State) {w : Nat} (big : Bool) (a n : Nat) (v : BitVec w) :
    withBytes s (s.mem.writeBits big a n v).bytes = { s with mem := s.mem.writeBits big a n v } :=
  rfl

theorem valB_false (n : Nat) (v : BitVec (n * 8)) : valB false n v = ProgE2E.bytesOf n v := by
  simp [valB, ProgE2E.bytesOf, Clif.Mem.byteIndex]

theorem getB_writeBits (cm : Clif.Mem) {w : Nat} (big : Bool) (a n : Nat) (v : BitVec w) :
    getB (cm.writeBits big a n v).bytes a n = valB big n v := by
  rw [ClifCStep.writeBits_bytes]
  exact bytesI.get_put_same cm.bytes a n _ (valB_length big n v)

/-! ## The match with other bytes -/

theorem match_mem {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {gn : Nat → Nat}
    {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {s s2 : Clif.State} {b k : Nat} {ρ : Nat → CV}
    {w w2 : ArmState} (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    (hf : s2.frame = s.frame) (hc : s2.callers = s.callers) (hmr : MR slots s2.mem w2) :
    Match f ctx R gn bl A MR slots s2 ⟨b, k, ρ, w2⟩ := by
  obtain ⟨hcall, hfunc, hslots, -, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  exact ⟨hc ▸ hcall, hf ▸ hfunc, hf ▸ hslots, hmr, B, j, hB, hf ▸ hterm, hj, hf ▸ hbd, hk,
    hf ▸ hheld, hf ▸ hcons⟩

/-! ## VCode side -/

/-- **A thread step leaves its events' writes on the patched memory.** -/
theorem vtstep_mem {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {b k : Nat} {ρ : Nat → CV} {w : ArmState} {evs : List Ev} {c'' : VConf CV ArmState}
    (h : VTStep vc sem ev (.run ⟨b, k, ρ, w⟩) evs c'') :
    (confW c'').mem = applyW evs (patch evs w).mem := by
  obtain ⟨vb, i, ops, hb, hi, hops, hf, hst⟩ := vtstep_foot h
  cases hst with
  | step hb2 hi2 hops2 hsem hlen hnx =>
    rw [hb] at hb2; cases hb2
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
    have e := hf.2 (patch evs w).mem hf.1
    rw [setMem_self, hsem] at e
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, hw, -⟩ := e
    cases hnx <;> simp only [confW] <;> rw [hw] <;> rfl

end Concurrency.IselMem
