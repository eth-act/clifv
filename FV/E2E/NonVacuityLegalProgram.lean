import FV.E2E.LegalSource
import FV.E2E.LinkPlace
import FV.Opt.Proof.LegalRust

/-!
# Non-vacuity of the whole-program refinement of the original `i128` program (S3)

The closed program `P = {add128, caller, plain}` under the trusted Rust environment
`Clif.Rust.env`:

* `add128(i128, i128) -> i128` (`v2 = iadd.i128 v0, v1`): legalised (two `i64` pairs in, one
  out);
* `caller(i64, i64) -> i64`: builds an `i128` from its arguments (`iconcat`), calls `add128` on it
  twice (an original-`i128` call between functions of the program, legalised to the split call),
  returns the low half (`ireduce`): legalised, its signature unchanged;
* `plain(i64) -> i64`: calls `caller`; no `i128` (the identity).

`ctx`: `P` is in the source domain (`ProgCtx`; `legalOkB` of each function, no validator run).
`plain_refines`: the whole-program run of `plain(5)` returns `10`; `legalProg_refines` gives the
legalised program's run of `plain` the same return. `add_refines`: the run of `add128` on two
`i128` values returns their sum; the theorem gives the legalised program's run of the legalised
`add128` on the split arguments the split sum. Both runs from the empty memory (no allocation:
`bounded_of_noSlots`).
-/

namespace E2E.LegalProgram.Witness

open Clif Opt.Legal Opt.Legalize128 E2E.LinkCheck

/-- `add128(i128, i128) -> i128`. -/
def addF : Function := Opt.Legal.Complete.Witness.add128

/-- `caller(i64, i64) -> i64`: `v2 = iconcat.i64 v0, v1; v3 = call add128(v2, v2);
v4 = ireduce.i64 v3; return v4`. -/
def callerF : Function where
  name := "caller"
  sig := { params := [{ ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }] }
  externs := [(0, { name := "add128", sig := addF.sig })]
  blocks := [{ id := 0, params := [(0, .i64), (1, .i64)],
               body := [{ results := [2], inst := .iconcat .i64 0 1 },
                        { results := [3], inst := .call 0 [2, 2] },
                        { results := [4], inst := .ireduce .i64 3 }],
               term := .ret [4] }]

/-- `plain(i64) -> i64`: `v1 = call caller(v0, v0); return v1` (no `i128`). -/
def plainF : Function where
  name := "plain"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  externs := [(0, { name := "caller", sig := callerF.sig })]
  blocks := [{ id := 0, params := [(0, .i64)],
               body := [{ results := [1], inst := .call 0 [0, 0] }], term := .ret [1] }]

def P : Program := { funcs := [addF, callerF, plainF] }

theorem legalOk : ∀ f ∈ P.funcs, legalOkB f = true := by decide

theorem plain_identity : legalize plainF = plainF :=
  Opt.Legal.Complete.legalize_of_not_mentions (by decide)

theorem caller_legalised : mentions128 callerF = true ∧ legalize callerF ≠ callerF := by decide

theorem indFree_legal : ∀ g ∈ (legalProg P).funcs, indFreeB g = true := by decide

/-- **`P` is in the source domain.** -/
theorem ctx : ProgCtx P Clif.Rust.env (fun _ => none) where
  ok := legalOk
  nd := by decide
  free f hf := linkFreeB_sound (by revert f; decide)
  free' f hf := linkFreeB_sound (by revert f; decide)
  decl g hg := declSigB_sound (by revert g; decide)
  decl' g hg := declSigB_sound (by revert g; decide)
  helpers op := by cases op <;> decide
  base _ := ⟨Clif.Rust.helperOk_env, Clif.Rust.extLegal_env, Clif.Rust.envKeepsAllocs_env.bounded⟩
  ind := fun ⟨g, hg, hn⟩ => absurd (indFreeB_sound (indFree_legal g hg)) hn

/-! ## Runs without allocation -/

/-- Every frame of `s` has no stack slot. -/
def SlotsNil (s : State) : Prop := ∀ fr ∈ s.frame :: s.callers.map (·.1), fr.slots = []

theorem enterFunc_slotsNil {g : Function} (hg : g.slots = []) {vals : List Val} {mem mem' : Mem}
    {fr : Frame} (h : enterFunc g vals mem = .ok (fr, mem')) : fr.slots = [] := by
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok h
  have := (Opt.enterSlots_ids g mem).1
  rw [hal, hg] at this
  exact List.map_eq_nil_iff.mp this

/-- **Bounded memories without allocation**: in a program whose functions have no stack slot,
under externs creating no allocation, every state reachable from a state with bounded memory
and slotless frames has bounded memory. -/
theorem bounded_of_noSlots {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hS : ∀ g ∈ P.funcs, g.slots = []) {env : Env} (hk : Clif.EnvKeepsAllocs env) {s : State}
    (hI : LInv P s) (hsl : SlotsNil s) (hM : MemBounded s.mem) :
    ∀ s', SReach env P s s' → MemBounded s'.mem := by
  have key : ∀ t t', SReach env P t t' → LInv P t → SlotsNil t → AllocInv s.mem t →
      LInv P t' ∧ SlotsNil t' ∧ AllocInv s.mem t' := by
    intro t t' h
    induction h with
    | refl => exact fun a b c => ⟨a, b, c⟩
    | step hs _ ih =>
      rename_i t0 t1 _
      intro hIt hst hat
      have hI1 := (step_next_linv hP hIt hs).1
      refine ih hI1 ?_ ((allocInv_step hP hk hIt hat).1 _ hs)
      rcases step_next_cases hP hIt hs with ⟨hc, hsl1, -⟩ | ⟨c, hc, hcs, g, vals, he⟩ |
        ⟨c, hc, hsl1, -⟩
      · intro fr hfr
        simp only [List.mem_cons, hc] at hfr
        rcases hfr with rfl | hfr
        · rw [hsl1]; exact hst _ (List.mem_cons_self ..)
        · exact hst fr (List.mem_cons_of_mem _ hfr)
      · have hgf : t0.frame.func = g := by
          obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
          rw [hfr]
        have hgP : g ∈ P.funcs := hgf ▸ hI1.1.1
        intro fr hfr
        simp only [List.mem_cons, hc, List.map_cons] at hfr
        rcases hfr with rfl | rfl | hfr
        · exact enterFunc_slotsNil (hS g hgP) he
        · rw [hcs]; exact hst _ (List.mem_cons_self ..)
        · exact hst fr (List.mem_cons_of_mem _ hfr)
      · intro fr hfr
        simp only [List.mem_cons] at hfr
        rcases hfr with rfl | hfr
        · rw [hsl1]; exact hst c.1 (by simp [hc])
        · exact hst fr (by simp only [hc, List.map_cons, List.mem_cons]; exact .inr (.inr hfr))
  intro s' hr a n hv
  have hat : AllocInv s.mem s := fun x hx => .inl fun a k hc =>
    List.any_eq_true.mpr ⟨x, hx, hc⟩
  obtain ⟨-, hsl', hat'⟩ := key s s' hr hI hsl hat
  simp only [Mem.valid, List.any_eq_true] at hv
  obtain ⟨x, hx, hc⟩ := hv
  rcases hat' x hx with h | h
  · exact hM a n (h a n hc)
  · have : slotBases s' = [] := by
      simp only [slotBases, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
      exact hsl'
    rw [this] at h
    cases h

theorem empty_bounded : MemBounded Mem.empty := fun a n h => by
  simp [Mem.valid, Mem.empty] at h

/-! ## The witnesses -/

theorem free : ∀ g ∈ P.funcs, LinkFree g := ctx.free
theorem noSlots : ∀ g ∈ P.funcs, g.slots = [] := by decide
theorem keepsAllocs : Clif.EnvKeepsAllocs Clif.Rust.env := fun n g hg vals m rv m' hr x hx => by
  rw [Clif.Rust.envKeepsAllocs_env n g hg vals m rv m' hr] at hx; exact hx

/-- Good states of a returning run from a slotless entry with the empty memory. -/
theorem good_of_run {h : Function} (hh : h ∈ P.funcs) {vals : List Val} {fr : Frame} {m1 : Mem}
    (he : enterFunc h vals Mem.empty = .ok (fr, m1)) {N : Nat} {rv : List Val} {m2 : Mem}
    (hr : Clif.runLoop Clif.Rust.env P N ⟨fr, [], m1⟩ = .returned rv m2) :
    GoodFrom Clif.Rust.env P (SomeInd (legalProg P)) (fun _ => none) ⟨fr, [], m1⟩ := by
  have hI : LInv P ⟨fr, [], m1⟩ := ⟨LFrame.enterFunc hh he, fun _ h => nomatch h⟩
  have hsl : SlotsNil ⟨fr, [], m1⟩ := fun fr' hfr' => by
    simp only [List.map_nil, List.mem_singleton] at hfr'
    subst hfr'
    exact enterFunc_slotsNil (noSlots h hh) he
  have hM : MemBounded m1 := by
    obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
    have hs : enterSlots h Mem.empty = ([], Mem.empty) := by
      simp [enterSlots, Mem.empty, noSlots h hh, bumpSlots]
    rw [hs] at hal
    simp only [Prod.mk.injEq] at hal
    rw [← hal.2]
    exact empty_bounded
  intro s' hs'
  refine ⟨bounded_of_noSlots free noSlots keepsAllocs hI hsl hM s' hs',
    memTrapFree_of_returned N _ rv m2 hr s' hs', fun ⟨g, hg, hn⟩ => ?_⟩
  exact absurd (indFreeB_sound (indFree_legal g hg)) hn

/-- A whole-program run from the entry of a function of `P` by `runWith`. -/
theorem run_of_runWith {h : Function} {n : String} (hp : P.func? n = some h) {vals : List Val}
    {fr : Frame} {m1 : Mem} (he : enterFunc h vals Mem.empty = .ok (fr, m1)) {N : Nat}
    {rv : List Val} (hr : (Clif.runWith Clif.Rust.env P n vals Mem.empty N).returnedVals? = some rv) :
    ∃ m2, Clif.runLoop Clif.Rust.env P N ⟨fr, [], m1⟩ = .returned rv m2 := by
  have hi : initState P n vals Mem.empty = .ok ⟨fr, [], m1⟩ :=
    (initState_ok_iff hp).mpr ⟨fr, m1, he, rfl⟩
  simp only [Clif.runWith, hi] at hr
  cases ho : Clif.runLoop Clif.Rust.env P N ⟨fr, [], m1⟩ with
  | returned v m => rw [ho] at hr; simp only [Outcome.returnedVals?_returned, Option.some.injEq] at hr; exact ⟨m, by rw [hr]⟩
  | _ => rw [ho] at hr; simp [Outcome.returnedVals?] at hr

theorem expRel_plain_refl {ps : List AbiParam} (hp : ∀ p ∈ ps, p.ty ≠ .i128) {vs : List Val}
    (hl : vs.length = ps.length) : ExpRel ((groups ps).getD []) vs vs := by
  obtain ⟨gs, hgs, hG⟩ := groups_plain hp
  rw [hgs, Option.getD_some]
  exact expRel_refl_plain hG hp hl

/-- **`plain(5)`** (no `i128`, calling the legalised `caller`): the source run returns `10`, and
`legalProg_refines` gives the legalised program's run the same return. -/
theorem plain_refines : ∃ fr m1 m2 k,
    enterFunc plainF [⟨.i64, 5⟩] Mem.empty = .ok (fr, m1) ∧
    Clif.runLoop Clif.Rust.env P 40 ⟨fr, [], m1⟩ = .returned [⟨.i64, 10⟩] m2 ∧
    Clif.runLoop Clif.Rust.env (legalProg P) k ⟨fr, [], m1⟩ = .returned [⟨.i64, 10⟩] m2 := by
  obtain ⟨⟨fr, m1⟩, he⟩ : ∃ r, enterFunc plainF [⟨.i64, 5⟩] Mem.empty = .ok r := ⟨_, rfl⟩
  obtain ⟨m2, hr⟩ := run_of_runWith (n := "plain") (by decide) he (N := 40)
    (rv := [⟨.i64, 10⟩]) (by decide)
  have hh : plainF ∈ P.funcs := by decide
  have hE : EntryRel plainF [⟨.i64, 5⟩] [⟨.i64, 5⟩] fr fr :=
    EntryRel.of_enter ⟨by rw [plain_identity], by rw [plain_identity]⟩ he
      (by rw [plain_identity]; exact he) (expRel_plain_refl (by decide) rfl)
  obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines ctx hh hE (good_of_run hh he hr) 40).1 _ _ hr
  have : rv' = [⟨.i64, 10⟩] := by
    obtain ⟨rg, hrg, hR⟩ := groups_plain (ps := plainF.sig.returns) (by decide)
    rw [hrg, Option.getD_some] at hrel
    exact expRel_val hR (by decide) hrel
  exact ⟨fr, m1, m2, k, he, hr, this ▸ hk⟩

/-- **`add128` on two `i128` values** (legalised; its arguments and result split into `i64`
halves): the source run returns the sum `2^64 + 8`; `legalProg_refines` gives the legalised
`add128`'s run on the split arguments `3, 1, 5, 0` the split sum `8, 1`. -/
theorem add_refines : ∃ fr fr' m1 m2 k,
    enterFunc addF [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩] Mem.empty = .ok (fr, m1) ∧
    enterFunc (legalize addF) [⟨.i64, 3#64⟩, ⟨.i64, 1#64⟩, ⟨.i64, 5#64⟩, ⟨.i64, 0#64⟩] Mem.empty =
      .ok (fr', m1) ∧
    Clif.runLoop Clif.Rust.env P 40 ⟨fr, [], m1⟩ = .returned [⟨.i128, 1#64 ++ 8#64⟩] m2 ∧
    Clif.runLoop Clif.Rust.env (legalProg P) k ⟨fr', [], m1⟩ =
      .returned [⟨.i64, 8#64⟩, ⟨.i64, 1#64⟩] m2 := by
  obtain ⟨⟨fr, m1⟩, he⟩ : ∃ r, enterFunc addF [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩]
      Mem.empty = .ok r := ⟨_, rfl⟩
  have hgs : groups addF.sig.params = some [[.lo, .hi], [.lo, .hi]] := rfl
  have hexp : ExpRel ((groups addF.sig.params).getD [])
      [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩]
      [⟨.i64, 3#64⟩, ⟨.i64, 1#64⟩, ⟨.i64, 5#64⟩, ⟨.i64, 0#64⟩] := by
    rw [hgs, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hh : addF ∈ P.funcs := by decide
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk addF hh) he hexp
  obtain ⟨m2, hr⟩ := run_of_runWith (n := "add128") (by decide) he (N := 40)
    (rv := [⟨.i128, 1#64 ++ 8#64⟩]) (by decide)
  have hfacts := legalFacts (legalOk addF hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines ctx hh hE (good_of_run hh he hr) 40).1 _ _ hr
  have hrg : groups addF.sig.returns = some [[.lo, .hi]] := rfl
  rw [hrg, Option.getD_some] at hrel
  obtain ⟨a, b, rest, rfl, ⟨l, hh', e1, rfl, rfl⟩, hrest⟩ : ∃ a b rest, rv' = a :: b :: rest ∧
      Halves ⟨.i128, 1#64 ++ 8#64⟩ a b ∧ ExpRel [] [] rest := by
    match rv', hrel with
    | a :: b :: rest, ⟨hv, hr⟩ => exact ⟨a, b, rest, rfl, hv, hr⟩
  cases rest with
  | cons => exact absurd hrest id
  | nil =>
    obtain ⟨-, e1⟩ := Val.mk.inj e1
    have hl : l = 8#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 0 64 = 8#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_right (a := hh')).symm.trans h2
    have hh2 : hh' = 1#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 64 64 = 1#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_left (b := l)).symm.trans h2
    subst hl hh2
    exact ⟨fr, fr', m1, m2, k, he, he', hr, hk⟩

end E2E.LegalProgram.Witness
