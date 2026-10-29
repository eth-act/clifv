module

public import FV.E2E.LinkPlace
public import FV.E2E.LegalProgram

@[expose] public section

/-! # Bounded memories of whole-program runs from a stack budget (A2/B1)

The source theorems of the executable compilers took `∀ s', SReach … cs s' → MemBounded s'.mem`
as a premise: `Clif.run`'s allocations need not lie below `2^64`. Here that bound is derived for
the runs the compiler theorems consider:

* `bounded_slotless`: every function the run enters has no stack slot, and the externs keep
  valid ranges below `2^64` (`EnvKeepsBounded`);
* `bounded_placed`: the slot-placement oracle (`Clif.Mem.place`) places every entered function's
  slots in its frame below its caller's stack pointer, and the stack pointers never wrap: each
  activation of `g` at call depth `k` has `β k g` bytes below its stack pointer, and entering
  `h` from it drops a frame `d` holding `h`'s slots with `d + β (k + 1) h ≤ β k g`
  (`β k _ = D * (d - k)` for a run of call depth `d`; `β _ g` the callees' budget of `g` without
  recursion). The externs keep the oracle and valid ranges below `2^64`.

Both start from the shapes of a whole-program step with the function entered and how it was
reached (`step_next_rich`). -/

namespace E2E.SrcBounded
set_option autoImplicit false
open Clif Opt.Legal

/-! ## How a step enters a function -/

/-- `h` is entered from an activation of `g` (memory `mem`): `g` declares it, or an indirect call
of `g` at a call-site signature matching `h`'s reaches it through a link-time address. -/
def EnterVia (p : Program) (g h : Function) (mem : Mem) : Prop :=
  (∃ e ∈ g.externs.map (·.2), p.func? e.name = some h) ∨
  (h ∈ p.funcs ∧ ∃ sig d, IndSite g sig ∧ g.sigDecls.lookup sig = some d ∧
    d.abiMatch h.sig = true ∧ ∃ a, mem.symbols h.name = some a)

/-- **The shapes of a whole-program step**, with the running functions: a step of the running
frame (allocations and oracle kept, or an extern's memory), entering a function (`EnterVia`), or
returning to the caller. -/
def RichShape (env : Env) (p : Program) (s s1 : State) : Prop :=
  (s1.callers = s.callers ∧ s1.frame.func = s.frame.func ∧
    ((s1.mem.place = s.mem.place ∧ s1.mem.allocs = s.mem.allocs) ∨
      ∃ n g vals rv, env.extern n = some g ∧ g vals s.mem = .returned rv s1.mem)) ∨
  (∃ c, s1.callers = c :: s.callers ∧ c.1.func = s.frame.func ∧
    ∃ h vals, EnterVia p s.frame.func h s.mem ∧ enterFunc h vals s.mem = .ok (s1.frame, s1.mem)) ∨
  (∃ c, s.callers = c :: s1.callers ∧ s1.frame.func = c.1.func ∧
    s1.mem = (s.mem.free (s.frame.slots.map (·.2))).leave)

theorem callCont_rich {env : Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {s1 : State}
    (h : Opt.callCont env p t rest rs ext vals = .next s1) :
    (s1.callers = ({ t.frame with body := rest }, rs) :: t.callers ∧
      ∃ g, p.func? ext.name = some g ∧ enterFunc g vals t.mem = .ok (s1.frame, s1.mem)) ∨
    (s1.callers = t.callers ∧ (∃ regs, s1.frame = { t.frame with regs, body := rest }) ∧
      ∃ n g rv, env.extern n = some g ∧ g vals t.mem = .returned rv s1.mem) := by
  unfold Opt.callCont at h
  split at h
  · rename_i g hg
    split at h
    · obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
      cases h
      exact .inl ⟨rfl, g, hg, he⟩
    · cases h
  · split at h
    · rename_i gsem hgs
      split at h
      · rename_i rvals mem' hr
        split at h
        · unfold continueWith at h
          split at h
          · rename_i regs _
            cases h
            exact .inr ⟨rfl, ⟨regs, rfl⟩, ext.name, gsem, rvals, hgs, hr⟩
          · cases h
        · cases h
      all_goals cases h
    · cases h

theorem indCont_rich {env : Env} {p : Program} {t : State} {rest : List Stmt} {rs : List ValueId}
    {sig : Nat} {d : Signature} {a : Nat} {v : List Val} {s1 : State}
    (h : indCont env p t rest rs sig d a v = .next s1) :
    (s1.callers = ({ t.frame with body := rest }, rs) :: t.callers ∧
      ∃ g, g ∈ p.funcs ∧ d.abiMatch g.sig = true ∧ t.mem.symbols g.name = some a ∧
        enterFunc g v t.mem = .ok (s1.frame, s1.mem)) ∨
    (s1.callers = t.callers ∧ (∃ regs, s1.frame = { t.frame with regs, body := rest }) ∧
      ∃ n g rv, env.extern n = some g ∧ g v t.mem = .returned rv s1.mem) := by
  rcases indCont_next h with ⟨hc1, -⟩ | h2
  · refine .inl ⟨hc1, ?_⟩
    unfold indCont at h
    split at h
    · rename_i g hg
      split at h
      · rename_i hm
        obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
        cases h
        exact ⟨g, List.mem_of_find?_eq_some hg, hm, by simpa using List.find?_some hg, he⟩
      · cases h
    · obtain ⟨⟨rv, mem'⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      dsimp only at h
      unfold continueWith at h
      split at h
      · injection h with h
        subst h
        exact absurd hc1 (by simp)
      · cases h
  · exact .inr h2

/-- The function of an `LFrame` at an indirect call has that indirect call site. -/
theorem indSite_of_stmt {P : Program} {fr : Frame} (hf : LFrame P fr) {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {sig : Nat} {callee : ValueId}
    {args : List ValueId} (hi : st.inst = .callIndirect sig callee args) : IndSite fr.func sig := by
  rcases hf with ⟨-, ⟨b, hbm, hsuf, -⟩ | ⟨hnil, -⟩⟩
  · rw [hb] at hsuf
    exact .inl ⟨b, hbm, st, hsuf.subset (List.mem_cons_self ..), callee, args, hi⟩
  · rw [hnil] at hb; cases hb

theorem indSite_of_term {P : Program} {fr : Frame} (hf : LFrame P fr) {callee : ValueId}
    {args : List ValueId} {et : ExnTable} (ht : fr.term = .tryCallIndirect callee args et) :
    IndSite fr.func et.sig := by
  rcases hf with ⟨-, ⟨b, hbm, -, hbt⟩ | ⟨-, bc, hj⟩⟩
  · exact .inr ⟨b, hbm, callee, args, et, by rw [← hbt, ht], rfl⟩
  · rw [hj] at ht; cases ht

theorem step_next_rich {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s s1 : State}
    (hI : LInv P s) (h : step env P s = .next s1) : RichShape env P s s1 := by
  -- a direct call from `t` (`s` up to `body`/`term`) of a declared extern
  have hcall : ∀ (t : State) rest rs ext vals, t.callers = s.callers →
      t.frame.func = s.frame.func → t.mem = s.mem →
      (∃ fn, s.frame.func.extern? fn = some ext) →
      Opt.callCont env P t rest rs ext vals = .next s1 → RichShape env P s s1 := by
    intro t rest rs ext vals htc htf htm ⟨fn, hfn⟩ hc
    rcases callCont_rich hc with ⟨hc1, g, hg, he⟩ | ⟨hc1, ⟨regs, hf1⟩, n, g, rv, hg, hr⟩
    · have hmem := Opt.Legal.Complete.lookup_mem hfn
      exact .inr (.inl ⟨_, by rw [hc1, htc], htf, g, vals,
        .inl ⟨ext, List.mem_map_of_mem (f := (·.2)) hmem, hg⟩, htm ▸ he⟩)
    · exact .inl ⟨hc1.trans htc, by rw [hf1]; exact htf, .inr ⟨n, g, vals, rv, hg, htm ▸ hr⟩⟩
  -- an indirect call from `t` at a call site of `s`'s function
  have hind : ∀ (t : State) rest rs sig d a v, t.callers = s.callers →
      t.frame.func = s.frame.func → t.mem = s.mem → IndSite s.frame.func sig →
      s.frame.func.sigDecls.lookup sig = some d →
      indCont env P t rest rs sig d a v = .next s1 → RichShape env P s s1 := by
    intro t rest rs sig d a v htc htf htm hsite hd hc
    rcases indCont_rich hc with ⟨hc1, g, hg, hm, hsym, he⟩ | ⟨hc1, ⟨regs, hf1⟩, n, g, rv, hg, hr⟩
    · exact .inr (.inl ⟨_, by rw [hc1, htc], htf, g, v,
        .inr ⟨hg, sig, d, hsite, hd, hm, a, htm ▸ hsym⟩, htm ▸ he⟩)
    · exact .inl ⟨hc1.trans htc, by rw [hf1]; exact htf, .inr ⟨n, g, v, rv, hg, htm ▸ hr⟩⟩
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨ext, vals⟩, hca, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hcall (tryState s bc) [] _ ext vals rfl rfl rfl
      ⟨fn, Opt.callArgs_extern (fr := (tryState s bc).frame) hca⟩ h
  · rw [step_tryInd env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨d, a, v⟩, hpre, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind (tryState s bc) [] _ _ d a v rfl rfl rfl (indSite_of_term hI.1 ht)
      (indPre_lookup (fr := (tryState s bc).frame) hpre) h
  · rw [step_ind env P s hb hi] at h
    obtain ⟨⟨d, a, v⟩, hpre, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind s rest st.results sig d a v rfl rfl rfl (indSite_of_stmt hI.1 hb hi)
      (indPre_lookup hpre) h
  · rw [Opt.step_eq_lift env P s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 =>
      rw [hl] at h; cases h
      exact .inl ⟨rfl, (Opt.lstep_next_frame hl).1, .inl (lstep_next_place hl)⟩
    | call ext vals rs rest =>
      rw [hl] at h
      obtain ⟨st, fn, args, -, -, -, hca⟩ := Opt.lstep_call_inv hl
      exact hcall s rest rs ext vals rfl rfl rfl ⟨fn, Opt.callArgs_extern hca⟩ h
    | ret vals =>
      rw [hl] at h
      obtain ⟨c, rs, cs, regs, hc, hc1, hf1⟩ := returnValues_next h
      exact .inr (.inr ⟨(c, rs), by rw [hc, hc1], by rw [hf1], returnValues_mem.1 s1 h⟩)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-! ## Runs entering only slotless functions -/

theorem enterSlots_noSlots {g : Function} (hs : g.slots = []) (mem : Mem) :
    ∃ pl, enterSlots g mem = ([], { mem with place := pl }) := by
  unfold enterSlots
  rw [hs]
  split
  · exact ⟨mem.place, rfl⟩
  · split
    · rw [initSlots_nil]; exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem free_valid {m : Mem} {bases : List Nat} {a n : Nat} (h : (m.free bases).valid a n = true) :
    m.valid a n = true := by
  simp only [Mem.valid, Mem.free, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨x, ⟨hx, -⟩, hc⟩ := h
  exact ⟨x, hx, hc⟩

theorem bounded_of_allocs {m m' : Mem} (h : m'.allocs = m.allocs) (hm : MemBounded m) :
    MemBounded m' := fun a n hv => hm a n (by simpa [Mem.valid, h] using hv)

theorem bounded_ret {m : Mem} {bases : List Nat} (h : MemBounded m) :
    MemBounded (m.free bases).leave := fun a n hv =>
  h a n (free_valid (by rwa [Mem.leave_valid] at hv))

/-- **Bounded memories, slotless entries**: in a run of a program without tail calls from a state
with bounded memory, under externs keeping valid ranges below `2^64`, if every function the run
enters has no stack slot, every reachable state has bounded memory. -/
theorem bounded_slotless {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsBounded env) {s : State} (hI : LInv P s) (hM : MemBounded s.mem)
    (hent : ∀ t t1, SReach env P s t → LInv P t → step env P t = .next t1 →
      t1.callers.length = t.callers.length + 1 →
      EnterVia P t.frame.func t1.frame.func t.mem → t1.frame.func.slots = []) :
    ∀ s', SReach env P s s' → MemBounded s'.mem := by
  have key : ∀ t t', SReach env P t t' → SReach env P s t → LInv P t → MemBounded t.mem →
      MemBounded t'.mem := by
    intro t t' h
    induction h with
    | refl => exact fun _ _ hm => hm
    | @step t0 t1 _ hs _ ih =>
      intro hr hIt hm
      have hr1 : SReach env P s t1 := hr.trans (.step hs (.refl _))
      refine ih hr1 (step_next_linv hP hIt hs).1 ?_
      rcases step_next_rich hP hIt hs with ⟨-, -, ⟨-, hal⟩ | ⟨n, g, vals, rv, hg, hret⟩⟩ |
        ⟨c, hc, -, h, vals, hvia, he⟩ | ⟨c, -, -, hm1⟩
      · exact bounded_of_allocs hal hm
      · exact hk n g hg vals _ rv _ hret hm
      · obtain ⟨_, _, _, _, _, _, hal, hfr⟩ := Opt.enterFunc_ok he
        have hh : t1.frame.func = h := by rw [hfr]
        have hsl := hent t0 t1 hr hIt hs (by rw [hc]; rfl) (by rw [hh]; exact hvia)
        rw [hh] at hsl
        obtain ⟨pl, hpl⟩ := enterSlots_noSlots hsl t0.mem
        rw [hpl] at hal
        obtain ⟨-, hm2⟩ := Prod.mk.inj hal
        rw [← hm2]
        exact bounded_of_allocs rfl hm
      · rw [hm1]; exact bounded_ret hm
  exact fun s' hr => key s s' hr (.refl _) hI hM

/-! ## Runs placing their slots in a stack that does not wrap -/

/-- The stack pointers `l` of the activations of the functions `fs` (the running one first): an
activation of `g` with `k` callers below it has `β k g` bytes below its stack pointer. -/
def SpOk (β : Nat → Function → Nat) : List (BitVec 64) → List Function → Prop
  | [], [] => True
  | sp :: l, g :: fs => β fs.length g ≤ sp.toNat ∧ SpOk β l fs
  | _, _ => False

/-- The functions of the activations of `s`, the running one first. -/
def funcs (s : State) : List Function := s.frame.func :: s.callers.map (·.1.func)

/-- The invariant of `bounded_placed`. -/
def PlacedInv (P : Program) (β : Nat → Function → Nat) (Q : Function → Prop)
    (fr : String → Option (Nat × (SlotId → Nat))) (sps : List (BitVec 64)) (t : State) : Prop :=
  LInv P t ∧ MemBounded t.mem ∧ Q t.frame.func ∧ (∀ c ∈ t.callers, Q c.1.func) ∧
    ∃ l, t.mem.place = some ⟨l ++ sps, fr, none⟩ ∧ SpOk β l (funcs t)

theorem toNat_sub_of_le {c : BitVec 64} {d : Nat} (h : d ≤ c.toNat) :
    (c - BitVec.ofNat 64 d).toNat = c.toNat - d := by
  have hc := c.isLt
  have hd : d < 2 ^ 64 := Nat.lt_of_le_of_lt h hc
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  omega

/-- **Bounded memories, placed slots**: in a run of a program without tail calls under externs
keeping the slot-placement oracle and valid ranges below `2^64`, from a state with bounded
memory whose oracle has the frames `fr` and the stack pointer `c` with `β 0` of its function
below it (`Q` of its function), if every entry of a function `h` from an activation of `g` with
`k` callers (`Q g`) drops a frame `d` with `d + β (k + 1) h ≤ β k g` that holds `h`'s slots (at
their offsets in `fr`; `Q h`), every reachable state has bounded memory. -/
theorem bounded_placed {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hkp : EnvKeepsPlace env) (hk : EnvKeepsBounded env)
    (β : Nat → Function → Nat) (Q : Function → Prop)
    (fr : String → Option (Nat × (SlotId → Nat))) {s : State} (hI : LInv P s)
    (hM : MemBounded s.mem) (hcs : s.callers = []) {c : BitVec 64} {sps : List (BitVec 64)}
    (hpl : s.mem.place = some ⟨c :: sps, fr, none⟩) (hc : β 0 s.frame.func ≤ c.toNat)
    (hQ : Q s.frame.func)
    (hent : ∀ t t1, SReach env P s t → LInv P t → Q t.frame.func → step env P t = .next t1 →
      t1.callers.length = t.callers.length + 1 → EnterVia P t.frame.func t1.frame.func t.mem →
      ∃ d off, fr t1.frame.func.name = some (d, off) ∧
        (∀ p ∈ t1.frame.func.slots, off p.1 + p.2.size ≤ d) ∧
        d + β (t.callers.length + 1) t1.frame.func ≤ β t.callers.length t.frame.func ∧
        Q t1.frame.func) :
    ∀ s', SReach env P s s' → MemBounded s'.mem := by
  have key : ∀ t t', SReach env P t t' → SReach env P s t → PlacedInv P β Q fr sps t →
      PlacedInv P β Q fr sps t' := by
    intro t t' h
    induction h with
    | refl => exact fun _ hi => hi
    | @step t0 t1 _ hs _ ih =>
      intro hr ⟨hIt, hm, hq, hqc, l, hpl0, hsp⟩
      have hr1 : SReach env P s t1 := hr.trans (.step hs (.refl _))
      have hI1 := (step_next_linv hP hIt hs).1
      refine ih hr1 ?_
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
        obtain ⟨d, off, hfd, hfit, hle, hqh⟩ :=
          hent t0 t1 hr hIt hq hs hlen (by rw [hh]; exact hvia)
        rw [hh] at hfd hfit hle hqh
        -- the running activation's stack pointer
        obtain ⟨sp, l', rfl⟩ : ∃ sp l', l = sp :: l' := by
          cases l with
          | nil => simp [funcs, SpOk] at hsp
          | cons sp l' => exact ⟨sp, l', rfl⟩
        have hsp0 : β t0.callers.length t0.frame.func ≤ sp.toNat := by
          simpa [funcs, SpOk] using hsp.1
        have hdle : d ≤ sp.toNat := by omega
        have hsub := toNat_sub_of_le hdle
        -- the slots placed below `sp`
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
  intro s' hr
  have h0 : PlacedInv P β Q fr sps s := by
    refine ⟨hI, hM, hQ, ?_, [c], ?_, ?_⟩
    · rw [hcs]; intro _ h; cases h
    · rw [hpl]; rfl
    · simp only [funcs, hcs, List.map_nil, SpOk, List.length_nil]
      exact ⟨hc, trivial⟩
  exact (key s s' hr (.refl _) h0).2.1

end E2E.SrcBounded
