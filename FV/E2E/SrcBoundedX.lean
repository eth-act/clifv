module

public import FV.Clif.LinkClifXN
public import FV.E2E.SrcBounded
public import FV.Opt.Proof.LegalSimX2

@[expose] public section

/-!
# Bounded memories of whole-program runs with unwinding from a stack budget (A2/B1, S10)

`E2E.SrcBounded` derives the bound `∀ s', SReach … cs s' → MemBounded s'.mem` on the source runs
from a stack budget. The theorems with unwinding take the same premise about the runs with
unwinding (`∀ u, ReachesX … cs.toX u → MemBounded u.s.mem`); it is derived the same way here:

* `srcBoundedX_slotless`: every function the run enters has no stack slot;
* `srcBoundedX_placed`: the slot-placement oracle places every entered function's slots in its
  frame below its caller's stack pointer, and the stack pointers never wrap (the budget `β` of
  `SrcBounded.bounded_placed`).

A step with unwinding is a step of `Clif.step` (`SrcBounded.step_next_rich`, `placedInv_step`),
or the raise of an extern that unwinds: its memory is the extern's (valid ranges below `2^64`,
`EnvKeepsBoundedX`; the oracle kept), caught by the raising frame itself (same frames), or by a
suspended caller after the frames above it have freed their slots and popped their stack
pointers (`unwindFrom_next_mem`). A `try_call`'s frame stays on the stack below its callee like
any caller (its slots stay allocated until it is left), so the budget covers it as a caller.

`reachesX_depth`: a run that ends within `N` steps reaches only states with fewer than `N`
callers (the call depth a stack budget must cover).
-/

namespace E2E.SrcBoundedX
set_option autoImplicit false
open Clif Opt.Legal Opt.Legal.X E2E.SrcBounded

/-! ## The steps that raise -/

/-- An exception raised at `xs` that continues: caught by the raising frame itself, at its
handler with the extern's memory, or propagated. -/
theorem raiseIn_next {xs xs' : XState} {e : Exn} {mem : Mem} (h : raiseIn xs e mem = .next xs') :
    (∃ fr, xs' = ⟨{ xs.s with frame := fr, mem := mem }, xs.tries⟩ ∧ fr.func = xs.s.frame.func) ∨
      unwindFrom e xs.s.frame xs.s.callers xs.tries mem = .next xs' := by
  unfold raiseIn at h
  split at h
  · rename_i r hr
    cases r with
    | ok fr =>
      simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
      obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
      exact .inl ⟨_, h.symm, rfl⟩
    | trap c => simp [XStepResult.ofRes] at h
    | stuck m => simp [XStepResult.ofRes] at h
  · exact .inr h

theorem free_leave_place (mem : Mem) (bs : List Nat) :
    ((mem.free bs).leave).place = mem.place.map fun pl => { pl with sps := pl.sps.tail } := by
  cases h : mem.place <;> simp [Mem.leave, Mem.free, h]

theorem free_leave_allocs {mem : Mem} {bs : List Nat} {x : Alloc}
    (h : x ∈ ((mem.free bs).leave).allocs) : x ∈ mem.allocs := by
  simp only [Mem.leave_allocs, Mem.free, List.mem_filter] at h
  exact h.1

/-- **An exception caught by a suspended caller**: the `k`-th caller resumes (its function,
the callers below it), the memory's allocations are among the raising memory's (the left frames'
slots freed), and the oracle has popped the `k + 1` left frames' stack pointers. -/
theorem unwindFrom_next_mem (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (xs' : XState), unwindFrom e fr cs ts mem = .next xs' →
      ∃ k c rs, cs[k]? = some (c, rs) ∧ xs'.s.callers = cs.drop (k + 1) ∧
        xs'.s.frame.func = c.func ∧ (∀ x ∈ xs'.s.mem.allocs, x ∈ mem.allocs) ∧
        xs'.s.mem.place = mem.place.map fun pl => { pl with sps := pl.sps.drop (k + 1) }
  | fr, [], _, mem, xs', h => by simp [unwindFrom] at h
  | fr, (c, rs) :: cs, t :: ts, mem, xs', h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r hr
      cases r with
      | ok fr' =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
        refine ⟨0, c, rs, rfl, rfl, rfl, fun x hx => free_leave_allocs hx, ?_⟩
        rw [free_leave_place]
        cases mem.place <;> simp
      | trap c => simp [XStepResult.ofRes] at h
      | stuck m => simp [XStepResult.ofRes] at h
    · obtain ⟨k, c', rs', h1, h2, h3, h4, h5⟩ := unwindFrom_next_mem e c cs ts _ xs' h
      refine ⟨k + 1, c', rs', by simpa using h1, by simpa using h2, h3,
        fun x hx => free_leave_allocs (h4 x hx), ?_⟩
      rw [h5, free_leave_place]
      cases mem.place <;> simp [List.drop_tail]
  | fr, _ :: _, [], mem, xs', h => by simp [unwindFrom] at h

theorem bounded_sub {m m' : Mem} (h : ∀ x ∈ m'.allocs, x ∈ m.allocs) (hm : MemBounded m) :
    MemBounded m' := fun a n hv => hm a n (by
      simp only [Mem.valid, List.any_eq_true] at hv ⊢
      obtain ⟨x, hx, hc⟩ := hv
      exact ⟨x, h x hx, hc⟩)

/-! ## The call depth of a run that ends -/

theorem stepX_next_callers {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs xs' : XState} (hI : XInv P xs) (h : stepX env P xs = .next xs') :
    xs'.s.callers.length ≤ xs.s.callers.length + 1 := by
  unfold stepX at h
  split at h
  · rename_i e mem _
    rcases raiseIn_next h with ⟨fr, rfl, -⟩ | h
    · exact Nat.le_succ _
    · obtain ⟨k, c, rs, -, h2, -⟩ := unwindFrom_next_mem e _ _ _ _ _ h
      rw [h2, List.length_drop]
      omega
  · cases hs : step env.toEnv P xs.s with
    | next s1 =>
      rw [hs] at h
      simp only [liftStep, XStepResult.next.injEq] at h
      subst h
      rcases step_next_rich hP hI.1 hs with ⟨hc, -⟩ | ⟨c, hc, -⟩ | ⟨c, hc, -⟩
      · rw [hc]; exact Nat.le_succ _
      · rw [hc]; exact Nat.le_refl _
      · show s1.callers.length ≤ xs.s.callers.length + 1
        rw [hc, List.length_cons]; omega
    | _ => rw [hs] at h; simp [liftStep] at h

/-- **A run that ends within `N` steps reaches only states with fewer than `N` callers more than
its start.** -/
theorem reachesX_depth {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs t : XState} (h : ReachesX env P xs t) :
    XInv P xs → ∀ N, runLoopX env P N xs ≠ .outOfFuel →
      t.s.callers.length + 1 ≤ xs.s.callers.length + N := by
  induction h with
  | refl =>
    intro _ N hN
    cases N with
    | zero => exact absurd rfl hN
    | succ N => omega
  | @next a b c hs _ ih =>
    intro hI N hN
    cases N with
    | zero => exact absurd rfl hN
    | succ N =>
      have hle := stepX_next_callers hP hI hs
      have := ih (stepX_next_xinv hP hI hs) N (by simpa [runLoopX, hs] using hN)
      omega

/-! ## Runs entering only slotless functions -/

/-- A step with unwinding keeps the memory bounded when the function it enters has no slot. -/
theorem stepX_bounded_slotless {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : EnvKeepsBounded env.toEnv) (hkU : EnvKeepsBoundedX env) {t0 t1 : XState}
    (hI : XInv P t0) (hm : MemBounded t0.s.mem) (hs : stepX env P t0 = .next t1)
    (hent : t1.s.callers.length = t0.s.callers.length + 1 →
      EnterVia P t0.s.frame.func t1.s.frame.func t0.s.mem → t1.s.frame.func.slots = []) :
    MemBounded t1.s.mem := by
  unfold stepX at hs
  split at hs
  · rename_i e mem hra
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hra
    have hmb : MemBounded mem := hkU n g hg vals _ e mem hu hm
    rcases raiseIn_next hs with ⟨fr, rfl, -⟩ | hs'
    · exact hmb
    · obtain ⟨k, c, rs, -, -, -, hal, -⟩ := unwindFrom_next_mem e _ _ _ _ _ hs'
      exact bounded_sub hal hmb
  · cases hst : step env.toEnv P t0.s with
    | next s1 =>
      rw [hst] at hs
      simp only [liftStep, XStepResult.next.injEq] at hs
      subst hs
      rcases step_next_rich hP hI.1 hst with ⟨-, -, ⟨-, hal⟩ | ⟨n, g, vals, rv, hg, hret⟩⟩ |
        ⟨c, hc, -, h, vals, hvia, he⟩ | ⟨c, -, -, hm1⟩
      · exact bounded_of_allocs hal hm
      · exact hk n g hg vals _ rv _ hret hm
      · obtain ⟨_, _, _, _, _, _, hal, hfr⟩ := Opt.enterFunc_ok he
        have hh : s1.frame.func = h := by rw [hfr]
        have hsl := hent (by rw [hc]; rfl) (by rw [hh]; exact hvia)
        rw [hh] at hsl
        obtain ⟨pl, hpl⟩ := enterSlots_noSlots hsl t0.s.mem
        rw [hpl] at hal
        obtain ⟨-, hm2⟩ := Prod.mk.inj hal
        rw [← hm2]
        exact bounded_of_allocs rfl hm
      · rw [hm1]; exact bounded_ret hm
    | _ => rw [hst] at hs; simp [liftStep] at hs

/-- **Bounded memories of whole-program runs with unwinding, slotless entries**: in a run with
unwinding of a program without tail calls from a state with bounded memory, under externs keeping
valid ranges below `2^64` (returning or unwinding), if every function the run enters has no
stack slot, every reachable state has bounded memory. -/
theorem srcBoundedX_slotless {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : EnvKeepsBounded env.toEnv) (hkU : EnvKeepsBoundedX env) {xs : XState}
    (hI : XInv P xs) (hM : MemBounded xs.s.mem)
    (hent : ∀ t xs1, ReachesX env P xs t → XInv P t → stepX env P t = .next xs1 →
      xs1.s.callers.length = t.s.callers.length + 1 →
      EnterVia P t.s.frame.func xs1.s.frame.func t.s.mem → xs1.s.frame.func.slots = []) :
    ∀ u, ReachesX env P xs u → MemBounded u.s.mem := by
  have key : ∀ t t', ReachesX env P t t' → ReachesX env P xs t → XInv P t → MemBounded t.s.mem →
      MemBounded t'.s.mem := by
    intro t t' h
    induction h with
    | refl => exact fun _ _ hm => hm
    | @next t0 t1 _ hs _ ih =>
      intro hr hIt hm
      exact ih (hr.snoc hs) (stepX_next_xinv hP hIt hs)
        (stepX_bounded_slotless hP hk hkU hIt hm hs (hent t0 t1 hr hIt hs))
  exact fun u hr => key xs u hr (.refl _) hI hM

/-! ## Runs placing their slots in a stack that does not wrap -/

theorem spOk_length {β : Nat → Function → Nat} :
    ∀ {l : List (BitVec 64)} {fs : List Function}, SpOk β l fs → l.length = fs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, spOk_length h.2]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem spOk_drop {β : Nat → Function → Nat} :
    ∀ (j : Nat) {l : List (BitVec 64)} {fs : List Function}, SpOk β l fs →
      SpOk β (l.drop j) (fs.drop j)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | j + 1, _ :: _, _ :: _, h => spOk_drop j h.2
  | _ + 1, [], _ :: _, h => absurd h id
  | _ + 1, _ :: _, [], h => absurd h id

/-- **A step of `Clif.step` keeps `bounded_placed`'s invariant** (its step, for one step whose
entered function's frame fits). -/
theorem placedInv_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hkp : EnvKeepsPlace env) (hk : EnvKeepsBounded env) {β : Nat → Function → Nat}
    {Q : Function → Prop} {fr : String → Option (Nat × (SlotId → Nat))} {sps : List (BitVec 64)}
    {t0 t1 : State} (hinv : PlacedInv P β Q fr sps t0) (hs : step env P t0 = .next t1)
    (hent : t1.callers.length = t0.callers.length + 1 →
      EnterVia P t0.frame.func t1.frame.func t0.mem →
      ∃ d off, fr t1.frame.func.name = some (d, off) ∧
        (∀ p ∈ t1.frame.func.slots, off p.1 + p.2.size ≤ d) ∧
        d + β (t0.callers.length + 1) t1.frame.func ≤ β t0.callers.length t0.frame.func ∧
        Q t1.frame.func) :
    PlacedInv P β Q fr sps t1 := by
  obtain ⟨hIt, hm, hq, hqc, l, hpl0, hsp⟩ := hinv
  have hI1 := (step_next_linv hP hIt hs).1
  rcases step_next_rich hP hIt hs with ⟨hc1, hf1, hloc⟩ | ⟨cc, hc1, hcf, h, vals, hvia, he⟩ |
    ⟨cc, hc0, hf1, hm1⟩
  · -- a step of the running frame
    have hfs : funcs t1 = funcs t0 := by simp only [funcs, hc1, hf1]
    refine ⟨hI1, ?_, hf1 ▸ hq, hc1 ▸ hqc, l, ?_, hfs ▸ hsp⟩
    · rcases hloc with ⟨-, hal⟩ | ⟨n, g, vals, rv, hg, hret⟩
      · exact bounded_of_allocs hal hm
      · exact hk n g hg vals _ rv _ hret hm
    · rcases hloc with ⟨hp, -⟩ | ⟨n, g, vals, rv, hg, hret⟩
      · rw [hp]; exact hpl0
      · rw [hkp n g hg vals _ rv _ hret]; exact hpl0
  · -- entering `h`
    obtain ⟨_, _, _, _, _, _, hal, hfr⟩ := Opt.enterFunc_ok he
    have hh : t1.frame.func = h := by rw [hfr]
    have hlen : t1.callers.length = t0.callers.length + 1 := by rw [hc1]; rfl
    obtain ⟨d, off, hfd, hfit, hle, hqh⟩ := hent hlen (by rw [hh]; exact hvia)
    rw [hh] at hfd hfit hle hqh
    obtain ⟨sp, l', rfl⟩ : ∃ sp l', l = sp :: l' := by
      cases l with
      | nil => simp [funcs, SpOk] at hsp
      | cons sp l' => exact ⟨sp, l', rfl⟩
    have hsp0 : β t0.callers.length t0.frame.func ≤ sp.toNat := by
      simpa [funcs, SpOk] using hsp.1
    have hdle : d ≤ sp.toNat := by omega
    have hsub := toNat_sub_of_le hdle
    have hes : enterSlots h t0.mem = h.slots.foldl (placeStep (sp - BitVec.ofNat 64 d) off)
        ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, none⟩ }) := by
      simp only [enterSlots, hpl0, hfd, List.cons_append, List.headD]
      rfl
    rw [hes] at hal
    obtain ⟨-, hm2⟩ := Prod.mk.inj hal
    obtain ⟨-, -, h3, -⟩ := placeSlots_spec (sp - BitVec.ofNat 64 d) off h.slots
      ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, none⟩ })
    have h5 : (h.slots.foldl (placeStep (sp - BitVec.ofNat 64 d) off)
        ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, none⟩ })).2.place =
        some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, none⟩ :=
      (placeSlots_facts (sp - BitVec.ofNat 64 d) off h.slots
        ([], { t0.mem with place := some ⟨(sp - BitVec.ofNat 64 d) :: (sp :: l' ++ sps), fr, none⟩ })).1
    rw [hm2] at h3 h5
    refine ⟨hI1, fun a n hv => ?_, hh ▸ hqh, ?_, (sp - BitVec.ofNat 64 d) :: sp :: l', ?_, ?_⟩
    · simp only [Mem.valid, List.any_eq_true] at hv
      obtain ⟨x, hx, hcx⟩ := hv
      rcases h3 x hx with hx' | ⟨p, hp, rfl⟩
      · exact hm a n (by simp only [Mem.valid, List.any_eq_true]; exact ⟨x, hx', hcx⟩)
      · simp only [Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
        have := hfit p hp
        have := sp.isLt
        omega
    · rw [hc1]
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · rw [hcf]; exact hq
      · exact hqc c' hc'
    · rw [h5]; rfl
    · refine ⟨?_, ?_⟩
      · simp only [hh, hc1, List.length_map, List.length_cons]
        rw [hsub]; omega
      · simpa [funcs, hc1, hcf] using hsp
  · -- returning to the caller
    obtain ⟨sp, l', rfl⟩ : ∃ sp l', l = sp :: l' := by
      cases l with
      | nil => simp [funcs, SpOk] at hsp
      | cons sp l' => exact ⟨sp, l', rfl⟩
    refine ⟨hI1, by rw [hm1]; exact bounded_ret hm, ?_, ?_, l', ?_, ?_⟩
    · rw [hf1]; exact hqc cc (by rw [hc0]; exact List.mem_cons_self ..)
    · intro c' hc'; exact hqc c' (by rw [hc0]; exact List.mem_cons_of_mem _ hc')
    · rw [hm1]
      simp only [Mem.leave, Mem.free, hpl0, List.cons_append, List.tail_cons]
    · have := hsp.2
      simpa [funcs, hc0, hf1] using this

/-- **A step with unwinding keeps `bounded_placed`'s invariant**: a raise leaves the extern's
memory (bounded, the oracle kept), at the raising frame's handler or after the left frames freed
their slots and popped their stack pointers. -/
theorem placedInvX_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hkp : EnvKeepsPlace env.toEnv)
    (hkpU : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      m'.place = m.place)
    (hk : EnvKeepsBounded env.toEnv) (hkU : EnvKeepsBoundedX env) {β : Nat → Function → Nat}
    {Q : Function → Prop} {fr : String → Option (Nat × (SlotId → Nat))} {sps : List (BitVec 64)}
    {t0 t1 : XState} (hI : XInv P t0) (hinv : PlacedInv P β Q fr sps t0.s)
    (hs : stepX env P t0 = .next t1)
    (hent : t1.s.callers.length = t0.s.callers.length + 1 →
      EnterVia P t0.s.frame.func t1.s.frame.func t0.s.mem →
      ∃ d off, fr t1.s.frame.func.name = some (d, off) ∧
        (∀ p ∈ t1.s.frame.func.slots, off p.1 + p.2.size ≤ d) ∧
        d + β (t0.s.callers.length + 1) t1.s.frame.func ≤ β t0.s.callers.length t0.s.frame.func ∧
        Q t1.s.frame.func) :
    PlacedInv P β Q fr sps t1.s := by
  have hI1 := (stepX_next_xinv hP hI hs).1
  obtain ⟨-, hm, hq, hqc, l, hpl0, hsp⟩ := hinv
  unfold stepX at hs
  split at hs
  · rename_i e mem hra
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hra
    have hmb : MemBounded mem := hkU n g hg vals _ e mem hu hm
    have hmp : mem.place = some ⟨l ++ sps, fr, none⟩ := by rw [hkpU n g hg vals _ e mem hu, hpl0]
    rcases raiseIn_next hs with ⟨fr', rfl, hf'⟩ | hs'
    · refine ⟨hI1, hmb, by rw [hf']; exact hq, hqc, l, hmp, ?_⟩
      simpa [funcs, hf'] using hsp
    · obtain ⟨k, c, rs, hk1, h2, h3, hal, h5⟩ := unwindFrom_next_mem e _ _ _ _ _ hs'
      have hkl : k < t0.s.callers.length := (List.getElem?_eq_some_iff.1 hk1).1
      have hck : t0.s.callers[k] = (c, rs) := (List.getElem?_eq_some_iff.1 hk1).2
      have hll : l.length = t0.s.callers.length + 1 := by
        rw [spOk_length hsp]; simp [funcs]
      have hdrop : t0.s.callers.drop k = (c, rs) :: t0.s.callers.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hkl, hck]
      have hfs : funcs t1.s = (funcs t0.s).drop (k + 1) := by
        simp only [funcs, List.drop_succ_cons, ← List.map_drop, hdrop, List.map_cons, h2, h3]
      refine ⟨hI1, bounded_sub hal hmb, ?_, ?_, l.drop (k + 1), ?_, hfs ▸ spOk_drop (k + 1) hsp⟩
      · rw [h3]
        exact hqc (c, rs) (List.mem_iff_getElem?.2 ⟨k, hk1⟩)
      · rw [h2]
        exact fun c' hc' => hqc c' (List.mem_of_mem_drop hc')
      · rw [h5, hmp]
        simp only [Option.map_some]
        rw [List.drop_append_of_le_length (by omega)]
  · cases hst : step env.toEnv P t0.s with
    | next s1 =>
      rw [hst] at hs
      simp only [liftStep, XStepResult.next.injEq] at hs
      subst hs
      exact placedInv_step hP hkp hk ⟨hI.1, hm, hq, hqc, l, hpl0, hsp⟩ hst hent
    | _ => rw [hst] at hs; simp [liftStep] at hs

/-- **Bounded memories of whole-program runs with unwinding, placed slots**
(`SrcBounded.bounded_placed` with unwinding): in a run with unwinding of a program without tail
calls under externs keeping the slot-placement oracle and valid ranges below `2^64` (returning or
unwinding), from a state without callers with bounded memory whose oracle has the frames `fr` and
the stack pointer `c` with `β 0` of its function below it (`Q` of its function), if every entry of
a function `h` from an activation of `g` with `k` callers (`Q g`) drops a frame `d` with
`d + β (k + 1) h ≤ β k g` that holds `h`'s slots (at their offsets in `fr`; `Q h`), every
reachable state has bounded memory. -/
theorem srcBoundedX_placed {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hkp : EnvKeepsPlace env.toEnv)
    (hkpU : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      m'.place = m.place)
    (hk : EnvKeepsBounded env.toEnv) (hkU : EnvKeepsBoundedX env)
    (β : Nat → Function → Nat) (Q : Function → Prop)
    (fr : String → Option (Nat × (SlotId → Nat))) {xs : XState} (hI : XInv P xs)
    (hM : MemBounded xs.s.mem) (hcs : xs.s.callers = []) {c : BitVec 64} {sps : List (BitVec 64)}
    (hpl : xs.s.mem.place = some ⟨c :: sps, fr, none⟩) (hc : β 0 xs.s.frame.func ≤ c.toNat)
    (hQ : Q xs.s.frame.func)
    (hent : ∀ t xs1, ReachesX env P xs t → XInv P t → Q t.s.frame.func →
      stepX env P t = .next xs1 → xs1.s.callers.length = t.s.callers.length + 1 →
      EnterVia P t.s.frame.func xs1.s.frame.func t.s.mem →
      ∃ d off, fr xs1.s.frame.func.name = some (d, off) ∧
        (∀ p ∈ xs1.s.frame.func.slots, off p.1 + p.2.size ≤ d) ∧
        d + β (t.s.callers.length + 1) xs1.s.frame.func ≤ β t.s.callers.length t.s.frame.func ∧
        Q xs1.s.frame.func) :
    ∀ u, ReachesX env P xs u → MemBounded u.s.mem := by
  have key : ∀ t t', ReachesX env P t t' → ReachesX env P xs t → XInv P t →
      PlacedInv P β Q fr sps t.s → PlacedInv P β Q fr sps t'.s := by
    intro t t' h
    induction h with
    | refl => exact fun _ _ hi => hi
    | @next t0 t1 _ hs _ ih =>
      intro hr hIt hi
      exact ih (hr.snoc hs) (stepX_next_xinv hP hIt hs)
        (placedInvX_step hP hkp hkpU hk hkU hIt hi hs (hent t0 t1 hr hIt hi.2.2.1 hs))
  intro u hr
  have h0 : PlacedInv P β Q fr sps xs.s := by
    refine ⟨hI.1, hM, hQ, ?_, [c], ?_, ?_⟩
    · rw [hcs]; intro _ h; cases h
    · rw [hpl]; rfl
    · simp only [funcs, hcs, List.map_nil, SpOk, List.length_nil]
      exact ⟨hc, trivial⟩
  exact (key xs u hr (.refl _) hI h0).2.1

end E2E.SrcBoundedX
