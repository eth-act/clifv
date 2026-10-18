import FV.E2E.LinkClifRev
import FV.Opt.Proof.LegalDirect
import FV.Opt.Proof.LegalPre

/-!
# Whole-program refinement of the original `i128` program (S3)

`legalProg P` replaces every function of the CLIF program `P` by its legalisation
(`Opt.Legalize128.legalize`). **`prog_refines`**: on the source domain (`ProgCtx`: every function
in `legalOkB` — the pass is the identity or `Pre` holds and the pass succeeds —, distinct names,
no `return_call`, declarations of the program's functions with their signatures, no function
named like a `__*ti3` helper, the base environment's contracts where a function mentions
`i128`), a whole-program run of a function `h` of `P` from its entry that returns or traps
within `M` steps is matched by the whole-program run of `legalize h` in `legalProg P` from the
entry with the ABI-split arguments: the results split by `h`'s return groups (`ExpRel`), the same
memory, the same trap.

The proof is by induction on `M`. The source run is a per-function run of `P.bare` under the
linked environment (`runLoop_linkN`), and also under the *guarded* linked environment
(`guardEnv`: a callee's run is used only from entries whose whole-program states are good —
valid ranges below `2^64`, no load/store trap, the link-time symbols —, `guard_run`; every callee
entered by the source run is such an entry). The per-activation refinement then runs with two
environments (`Opt.Legal.legalize_refines2` for a legalised function, `ident_run` for an
identity one): the guarded source environment and the target's linked environment (`tgtEnv`),
related at every callee by the induction hypothesis (`extRel_prog`, `callIndRel_link`). The
target's per-function run is a whole-program run (`Clif.unlink_run`).
-/

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legalize128

/-! ## The legalised program -/

/-- The legalised program: every function replaced by its legalisation. -/
def legalProg (P : Program) : Program := { P with funcs := P.funcs.map legalize }

@[simp] theorem legalProg_funcs (P : Program) : (legalProg P).funcs = P.funcs.map legalize := rfl

theorem expandExterns_names : ∀ {es es' : List (FnRef × ExtFunc)}, expandExterns es = .ok es' →
    es'.map (·.2.name) = es.map (·.2.name)
  | [], es', h => by
    simp only [expandExterns, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | (r, e) :: es, es', h => by
    simp only [expandExterns] at h
    obtain ⟨s, -, h⟩ := except_bind_ok h
    obtain ⟨rest, hr, h⟩ := except_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [expandExterns_names hr]

theorem helperExts_names (f : Function) : (helperExts f).map (·.2.name) = helperNames f := by
  simp only [helperExts, List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst 0 (helperNames f)]
  apply List.map_congr_left
  intro x _
  rfl

/-- The output of a legalisation of a function mentioning `i128`. -/
theorem function128Cert_spec {f g : Function} {cert : Cert} (hm : mentions128 f = true)
    (h : function128Cert f = .ok (g, cert)) :
    ∃ es ds, expandExterns f.externs = .ok es ∧ expandSigDecls f.sigDecls = .ok ds ∧
      g.externs = es ++ helperExts f ∧ g.sigDecls = ds := by
  simp only [function128Cert, hm, Bool.not_true, Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  obtain ⟨sig, -, h⟩ := except_bind_ok h
  obtain ⟨es, hes, h⟩ := except_bind_ok h
  obtain ⟨ds, hds, h⟩ := except_bind_ok h
  obtain ⟨pg, -, h⟩ := except_bind_ok h
  obtain ⟨rg, -, h⟩ := except_bind_ok h
  obtain ⟨⟨bs', st'⟩, -, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨es, ds, hes, hds, rfl, rfl⟩

/-- Without `i128` the signatures of `f`, its externs and its call-site declarations do not
mention `i128`. -/
theorem not_mentions {f : Function} (h : mentions128 f = false) :
    sig128 f.sig = false ∧ (∀ e ∈ f.externs, sig128 e.2.sig = false) ∧
      ∀ d ∈ f.sigDecls, sig128 d.2 = false := by
  simp only [mentions128, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
  exact ⟨h.1.1.1, fun e he => h.1.1.2 e he, fun d hd => h.1.2 d hd⟩

theorem lookup_mem {α β : Type} [BEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : ∃ a', (a', b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.lookup] at h
    split at h
    · cases h; exact ⟨x.1, by simp⟩
    · obtain ⟨a', ha⟩ := ih h; exact ⟨a', List.mem_cons_of_mem _ ha⟩

/-- **The facts of the legalisation of a function of the source domain.** -/
structure LegalFacts (f : Function) : Prop where
  name : (legalize f).name = f.name
  slots : (legalize f).slots = f.slots
  sig : sigExp f.sig = some (legalize f).sig
  ext : ∀ fn e, f.extern? fn = some e →
    ∃ s', sigExp e.sig = some s' ∧ (legalize f).extern? fn = some { e with sig := s' }
  names : ∃ hn, (legalize f).externs.map (·.2.name) = f.externs.map (·.2.name) ++ hn ∧
    ∀ n ∈ hn, n ∈ helperNames f
  ind : ¬ IndFree f → ¬ IndFree (legalize f)

theorem legalFacts {f : Function} (h : legalOkB f = true) : LegalFacts f := by
  rcases Complete.legalOkB_cases h with ⟨hm, -, hl⟩ | ⟨hp, cert, hc⟩
  · obtain ⟨hs, he, -⟩ := not_mentions hm
    refine ⟨by rw [hl], by rw [hl], by rw [hl]; exact Complete.sigExp_plain hs, fun fn e hfe => ?_,
      ⟨[], by rw [hl, List.append_nil], fun _ h => by cases h⟩, fun h1 => by rw [hl]; exact h1⟩
    refine ⟨e.sig, ?_, by rw [hl]; exact hfe⟩
    obtain ⟨fn', hmem⟩ := lookup_mem hfe
    exact Complete.sigExp_plain (he _ hmem)
  · have hchk := Complete.check_complete hp hc
    have hG := check_good hchk
    obtain ⟨es, ds, hes, hds, he, hd⟩ := function128Cert_spec hp.mentions hc
    have hO := Complete.gok_of hes hds he hd cert
    refine ⟨hG.name, hG.slots, hG.sig, fun fn e hfe => hO.ext fn e hfe,
      ⟨helperNames f, by rw [he, List.map_append, expandExterns_names hes, helperExts_names],
        fun _ h => h⟩, fun hnf => ?_⟩
    -- an indirect call of `f` is a `call_indirect` statement (no `try_call_indirect`, `Pre`)
    have hci : ∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
        st.inst = .callIndirect sig callee args := by
      refine Classical.byContradiction fun hno => hnf fun B hB => ⟨fun st hst sig callee args hi =>
        hno ⟨B, hB, st, hst, sig, callee, args, hi⟩, fun c args et ht => hp.noTryInd B hB c args et ht⟩
    obtain ⟨B, hB, st, hst, sig, callee, args, hi⟩ := check_callInd hchk hci
    exact fun hif => (hif B hB).1 st hst sig callee args hi

/-- `Pre`: no indirect call site of `f` has an `i128` signature. -/
theorem pre_indSite {f : Function} (hp : Complete.Pre f) {sig : Nat} {d : Signature}
    (hs : IndSite f sig) (hd : f.sigDecls.lookup sig = some d) : sig128 d = false := by
  rcases hs with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, c, args, et, ht, -⟩
  · exact hp.callInd B hB st hst sig callee args hi d hd
  · exact absurd ht (hp.noTryInd B hB c args et)

theorem legalProg_names (P : Program) :
    (legalProg P).funcs.map (·.name) = P.funcs.map (·.name) ∨
      ¬ ∀ f ∈ P.funcs, legalOkB f = true := by
  by_cases h : ∀ f ∈ P.funcs, legalOkB f = true
  · refine .inl ?_
    simp only [legalProg_funcs, List.map_map]
    exact List.map_congr_left fun f hf => (legalFacts (h f hf)).name
  · exact .inr h

/-! ## Reachability -/

theorem _root_.Clif.StepsTo.sreach {env : Env} {p : Program} :
    ∀ {k : Nat} {s s1 : State}, StepsTo env p k s s1 → SReach env p s s1
  | 0, s, s1, h => by simp only [StepsTo] at h; rw [h]; exact .refl _
  | k + 1, s, s1, ⟨s', hs, h⟩ => .step hs (Clif.StepsTo.sreach h)

theorem _root_.Opt.Legal.SReach.steps {env : Env} {p : Program} {s s1 : State} (h : SReach env p s s1) :
    ∃ k, StepsTo env p k s s1 := by
  induction h with
  | refl s => exact ⟨0, rfl⟩
  | step hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, _, hs, hk⟩

theorem _root_.Opt.Legal.SReach.trans {env : Env} {p : Program} {a b c : State} (h1 : SReach env p a b)
    (h2 : SReach env p b c) : SReach env p a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem _root_.Opt.Legal.SReach.belowK {env : Env} {p : Program} (K : List (Frame × List ValueId)) {s s1 : State}
    (h : SReach env p s s1) : SReach env p (s.below K) (s1.below K) := by
  obtain ⟨k, hk⟩ := h.steps
  exact (StepsTo.below K hk).sreach

theorem memTrapFree_below {env : Env} {p : Program} {s : State} (K : List (Frame × List ValueId))
    (h : MemTrapFree env p (s.below K)) : MemTrapFree env p s := by
  intro c st rest hs hb
  refine h c st rest ?_ hb
  rw [step_below, hs]
  rfl

/-- A whole-program step that finishes returns a memory with fewer valid ranges. -/
theorem step_done_valid {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s : State}
    (hI : LInv P s) {v : List Val} {m : Mem} (h : step env P s = .done v m) :
    ∀ a n, m.valid a n = true → s.mem.valid a n = true := by
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h callCont_ne_done
  · rw [step_tryInd env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [step_ind env P s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [Opt.step_eq_lift env P s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals =>
      rw [hl] at h
      have hm := returnValues_mem.2 v m h
      intro a n hv
      rw [hm, Mem.leave_valid] at hv
      simp only [Mem.valid, Mem.free, List.any_eq_true, List.mem_filter] at hv ⊢
      obtain ⟨x, ⟨hx, -⟩, hx2⟩ := hv
      exact ⟨x, hx, hx2⟩
    | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-! ## Entering a function -/

theorem initState_ok_iff {P : Program} {n : String} {h : Function} (hp : P.func? n = some h)
    {vals : List Val} {mem : Mem} {s : State} :
    initState P n vals mem = .ok s ↔ ∃ fr mem', enterFunc h vals mem = .ok (fr, mem') ∧
      s = ⟨fr, [], mem'⟩ := by
  simp only [initState, hp, Res.ofOption_some, Res.ok_bind]
  cases he : enterFunc h vals mem with
  | ok r =>
    obtain ⟨fr, mem'⟩ := r
    simp only [Res.ok_bind, Res.pure_eq]
    constructor
    · intro e; cases e; exact ⟨fr, mem', rfl, rfl⟩
    · rintro ⟨fr2, mem2, e, rfl⟩; cases e; rfl
  | trap c => simp
  | stuck m => simp

theorem initState_not_trap (P : Program) (n : String) (vals : List Val) (mem : Mem) (c : TrapCode) :
    initState P n vals mem ≠ .trap c := by
  simp only [initState]
  cases P.func? n with
  | none => simp
  | some h =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases he : enterFunc h vals mem with
    | ok r => simp
    | trap c' => exact absurd he (Opt.enterFunc_not_trap h vals mem c')
    | stuck m => simp

/-- The entry of the legalisation of a function of the source domain on the ABI-split
arguments: the same slots and memory. -/
theorem enterFunc_legal {f : Function} (hok : legalOkB f = true) {vals vals' : List Val}
    {mem mem1 : Mem} {fr : Frame} (he : enterFunc f vals mem = .ok (fr, mem1))
    (hexp : ExpRel ((groups f.sig.params).getD []) vals vals') :
    ∃ fr', enterFunc (legalize f) vals' mem = .ok (fr', mem1) := by
  rcases Complete.legalOkB_cases hok with ⟨hm, -, hl⟩ | ⟨hp, cert, hc⟩
  · obtain ⟨hs, -, -⟩ := not_mentions hm
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hs)
    rw [hgs, Option.getD_some] at hexp
    rw [expRel_val hG (sig128_params hs) hexp, hl]
    exact ⟨fr, he⟩
  · have hchk := Complete.check_complete hp hc
    have hG : Good ⟨f, legalize f, cert⟩ := by
      rw [Complete.legalize_of_ok hc]; exact check_good hchk
    obtain ⟨b, regs, hb, hty, hbt, hr, hsl, -⟩ := Opt.enterFunc_ok he
    obtain ⟨b0, bs, b0', bs', hf, hg, -, hok0, -⟩ := hG.blocks
    simp only [Function.entry?] at hb
    rw [show f = (⟨f, legalize f, cert⟩ : Ctx).f from rfl, hf] at hb
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ite_true] at hok0
    obtain ⟨⟨-, -⟩, hok0⟩ := hok0
    split at hok0
    · rename_i gs z rest hgs hbody'
      simp only [Bool.and_eq_true, beq_iff_eq] at hok0
      obtain ⟨⟨hep, -⟩, -⟩ := hok0
      have hgs' : groups f.sig.params = some gs := hgs
      rw [hgs', Option.getD_some] at hexp
      obtain ⟨hty', -, -⟩ := entry_bind hep hexp hbt
      obtain ⟨gs0, rg0, hgs0, -, hpar', -⟩ := sigExp_spec hG.sig
      rw [hgs'] at hgs0
      cases hgs0
      have htyS : vals'.map (·.ty) = AbiParam.tys (legalize f).sig.params := by
        have := expRel_tys (groups_spec hgs') hexp (by rw [hty]; rfl)
        rw [this, hpar']
        rfl
      obtain ⟨regs', hr'⟩ := setMany_of_len Regs.empty (rs := b0'.params.map (·.1)) (vs := vals')
        (by have := congrArg List.length hty'; simpa using this.symm)
      have hb' : (legalize f).entry? = some b0' := by
        simp only [Function.entry?]
        rw [show legalize f = (⟨f, legalize f, cert⟩ : Ctx).g from rfl, hg]
        rfl
      have hslots : enterSlots (legalize f) mem = enterSlots f mem :=
        Opt.enterSlots_congr hG.name hG.slots mem
      refine ⟨⟨legalize f, regs', fr.slots, b0'.body, b0'.term⟩, ?_⟩
      rw [Opt.enterFunc_of hb' htyS hty' hr', hslots, hsl]
    · cases hok0

/-! ## The environments -/

/-- Some function of `P` has an indirect call. -/
def SomeInd (P : Program) : Prop := ∃ g ∈ P.funcs, ¬ IndFree g

/-- **Good whole-program states from `s`**: valid ranges below `2^64`, no load/store trap, the
link-time symbols `syms` (if `G`). -/
def GoodFrom (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat) (s : State) : Prop :=
  ∀ s', SReach B P s s' → MemBounded s'.mem ∧ MemTrapFree B P s' ∧ (G → s'.mem.symbols = syms)

/-- A call of `h` on `vals` from memory `mem` enters only at a good state. -/
def GoodCall (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat) (h : Function)
    (vals : List Val) (mem : Mem) : Prop :=
  ∀ fr' mem', enterFunc h vals mem = .ok (fr', mem') → GoodFrom B P G syms ⟨fr', [], mem'⟩

theorem GoodFrom.of_reach {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {s s1 : State} (h : GoodFrom B P G syms s) (hr : SReach B P s s1) : GoodFrom B P G syms s1 :=
  fun s' hs' => h s' (hr.trans hs')

/-- The callee run of the linked environment (`linkEnvN`). -/
def linkFun (B : Env) (P : Program) (M : Nat) (n : String) : List Val → Mem → Outcome :=
  fun vals mem => match initState P n vals mem with
    | .ok s => Clif.runLoop B P M s
    | .trap c => .trapped c
    | .stuck m => .stuck m

open Classical in
/-- The callee run of the guarded environment: the linked environment's from a good entry. -/
noncomputable def guardFun (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M : Nat) (h : Function) (n : String) : List Val → Mem → Outcome :=
  fun vals mem => if GoodCall B P G syms h vals mem then linkFun B P M n vals mem
    else .stuck "outside the source run"

theorem guardFun_good {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}
    {h : Function} {n : String} {vals : List Val} {mem : Mem}
    (hg : GoodCall B P G syms h vals mem) : guardFun B P G syms M h n vals mem = linkFun B P M n vals mem := by
  simp [guardFun, hg]

theorem guardFun_cases {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}
    {h : Function} {n : String} {vals : List Val} {mem : Mem} {o : Outcome}
    (ho : guardFun B P G syms M h n vals mem = o) (hs : ∀ msg, o ≠ .stuck msg) :
    GoodCall B P G syms h vals mem ∧ linkFun B P M n vals mem = o := by
  unfold guardFun at ho
  split at ho
  · exact ⟨‹_›, ho⟩
  · exact absurd ho.symm (hs _)

/-- **The guarded linked environment** of the source program `P`: a function `h` of `P` runs as
under `linkEnvN P B M`, but only from a good entry (`GoodCall`); every other extern is `B`'s. -/
noncomputable def guardEnv (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M : Nat) : Env where
  extern n := match P.func? n with
    | some h => some (guardFun B P G syms M h n)
    | none => B.extern n
  names := (linkEnvN P B M).names
  sigOf := (linkEnvN P B M).sigOf

theorem guardEnv_none {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}
    {n : String} (hn : P.func? n = none) : (guardEnv B P G syms M).extern n = B.extern n := by
  simp [guardEnv, hn]

theorem guardEnv_some {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}
    {n : String} {h : Function} (hn : P.func? n = some h) :
    (guardEnv B P G syms M).extern n = some (guardFun B P G syms M h n) := by
  simp [guardEnv, hn]

theorem linkEnvN_some' {B : Env} {P : Program} {M : Nat} {n : String} {h : Function}
    (hn : P.func? n = some h) : (linkEnvN P B M).extern n = some (linkFun B P M n) :=
  linkEnvN_some hn

theorem agree_guard (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat) (M : Nat) :
    EnvAgree P (linkEnvN P B M) (guardEnv B P G syms M) :=
  ⟨rfl, rfl, fun n hn => by rw [guardEnv_none hn, linkEnvN_none hn]⟩

/-- The callee run of the target's linked environment (`linkEnv`, unbounded). -/
noncomputable def tgtFun (B : Env) (P' : Program) (n : String) : List Val → Mem → Outcome :=
  fun vals mem => match initState P' n vals mem with
    | .ok s => runLim B P' s
    | .trap c => .trapped c
    | .stuck m => .stuck m

/-- **The target's linked environment**: a function of the legalised program `P'` runs its
whole-program run (unbounded, `linkEnv`), every other extern is `B`'s; an address resolves
through the source program's names (those of `P'` are the same functions, plus the helpers). -/
noncomputable def tgtEnv (B : Env) (P P' : Program) : Env where
  extern := (linkEnv P' B).extern
  names := P.names ++ B.names
  sigOf n := (P'.func? n).map (·.sig)

theorem tgtEnv_some {B : Env} {P P' : Program} {n : String} {h : Function}
    (hn : P'.func? n = some h) : (tgtEnv B P P').extern n = some (tgtFun B P' n) :=
  linkEnv_some hn

theorem tgtEnv_none {B : Env} {P P' : Program} {n : String} (hn : P'.func? n = none) :
    (tgtEnv B P P').extern n = B.extern n :=
  linkEnv_none hn

theorem runLim_ok {env : Env} {p : Program} {s : State} {o : Outcome} (h : runLim env p s = o)
    (ho : o ≠ .outOfFuel) : ∃ N, Clif.runLoop env p N s = o := by
  unfold runLim at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h.symm ho

/-! ## Unlinking instances -/

theorem func?_name {P : Program} (hnd : (P.funcs.map (·.name)).Nodup) {h : Function}
    (hh : h ∈ P.funcs) : P.func? h.name = some h := by
  cases e : P.func? h.name with
  | none => exact absurd rfl (Program.func?_none e h hh)
  | some g =>
    obtain ⟨hg, hgn⟩ := Program.func?_some e
    rw [name_inj hnd hg hh hgn]

/-- The program facts every unlinking needs. -/
structure ProgFacts (P : Program) : Prop where
  nd : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, LinkFree g
  decl : ∀ g ∈ P.funcs, ∀ fn e, g.extern? fn = some e → ∀ h, P.func? e.name = some h → h.sig = e.sig

/-- A callee run of the linked environment that returns or traps is the callee's whole-program
run. -/
theorem linkFun_prog {B : Env} {P : Program} {M : Nat} {h : Function} (hp : P.func? h.name = some h)
    (vals : List Val) (mem : Mem) :
    (∀ rv m', linkFun B P M h.name vals mem = .returned rv m' → ∃ fr' mem',
      enterFunc h vals mem = .ok (fr', mem') ∧ ∃ N, Clif.runLoop B P N ⟨fr', [], mem'⟩ = .returned rv m') ∧
    (∀ c, linkFun B P M h.name vals mem = .trapped c → ∃ fr' mem',
      enterFunc h vals mem = .ok (fr', mem') ∧ ∃ N, Clif.runLoop B P N ⟨fr', [], mem'⟩ = .trapped c) := by
  unfold linkFun
  cases hi : initState P h.name vals mem with
  | ok s =>
    obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
    exact ⟨fun rv m' hr => ⟨fr, mem', he, M, hr⟩, fun c hr => ⟨fr, mem', he, M, hr⟩⟩
  | trap c => exact absurd hi (initState_not_trap P h.name vals mem c)
  | stuck m => exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

theorem unlink_linkN {B : Env} {P : Program} (hF : ProgFacts P) (M : Nat) :
    Unlink (linkEnvN P B M) P B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := ⟨_, linkEnvN_some' (func?_name hF.nd hh), linkFun_prog (func?_name hF.nd hh)⟩
  base _ hn := linkEnvN_none hn
  sigOf _ := rfl

theorem unlink_guard {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M : Nat) : Unlink (guardEnv B P G syms M) P B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, guardEnv_some hp, fun vals mem => ⟨fun rv m' hr => ?_, fun c hr => ?_⟩⟩
    · obtain ⟨-, hl⟩ := guardFun_cases hr (fun _ h => by cases h)
      exact (linkFun_prog hp vals mem).1 rv m' hl
    · obtain ⟨-, hl⟩ := guardFun_cases hr (fun _ h => by cases h)
      exact (linkFun_prog hp vals mem).2 c hl
  base _ hn := guardEnv_none hn
  sigOf _ := rfl

theorem unlink_tgt {B : Env} {P P' : Program} (hF : ProgFacts P') : Unlink (tgtEnv B P P') P' B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, tgtEnv_some hp, fun vals mem => ⟨fun rv m' hr => ?_, fun c hr => ?_⟩⟩
    · unfold tgtFun at hr
      cases hi : initState P' h.name vals mem with
      | ok s =>
        rw [hi] at hr
        obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
        obtain ⟨N, hN⟩ := runLim_ok hr (fun h => by cases h)
        exact ⟨fr, mem', he, N, hN⟩
      | trap c => exact absurd hi (initState_not_trap P' h.name vals mem c)
      | stuck m => rw [hi] at hr; cases hr
    · unfold tgtFun at hr
      cases hi : initState P' h.name vals mem with
      | ok s =>
        rw [hi] at hr
        obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
        obtain ⟨N, hN⟩ := runLim_ok hr (fun h => by cases h)
        exact ⟨fr, mem', he, N, hN⟩
      | trap c' => exact absurd hi (initState_not_trap P' h.name vals mem c')
      | stuck m => rw [hi] at hr; cases hr
  base _ hn := tgtEnv_none hn
  sigOf _ := rfl

theorem unlinkInd_linked {E B : Env} {P : Program} {syms : String → Option Nat}
    (hS : IndScope P B syms) (hb : ∀ n, B.sigOf n = none) (hn : E.names = P.names ++ B.names) :
    UnlinkInd E P B syms :=
  ⟨hS, hb, P.externNames ++ B.names, by rw [hn, Program.names, List.append_assoc],
    fun _ h => h⟩

theorem unlinkInd_tgt {B : Env} {P P' : Program} {syms : String → Option Nat}
    (hS : IndScope P' B syms) (hb : ∀ n, B.sigOf n = none)
    (hnames : P'.funcs.map (·.name) = P.funcs.map (·.name))
    (hext : ∀ n ∈ P.externNames, n ∈ P'.externNames) : UnlinkInd (tgtEnv B P P') P' B syms :=
  ⟨hS, hb, P.externNames ++ B.names, by
    simp only [tgtEnv, Program.names, hnames, List.append_assoc], fun n hn => by
    rcases List.mem_append.mp hn with h | h
    · exact List.mem_append_left _ (hext n h)
    · exact List.mem_append_right _ h⟩

/-- `IndScope` of the source program from the legalised one's (the same functions, fewer
names). -/
theorem indScope_src {B : Env} {P P' : Program} {syms : String → Option Nat}
    (hS : IndScope P' B syms) (hnames : P'.funcs.map (·.name) = P.funcs.map (·.name))
    (hext : ∀ n ∈ P.externNames, n ∈ P'.externNames)
    (hfunc : ∀ n, P.func? n = none → P'.func? n = none) : IndScope P B syms where
  keep := hS.keep
  inj := by rw [← hnames]; exact hS.inj
  alias a ha b hb x hxa hxb hpa hpb := by
    have hsub : ∀ n ∈ P.names ++ B.names, n ∈ P'.names ++ B.names := fun n hn => by
      simp only [Program.names, List.mem_append] at hn ⊢
      rcases hn with (h | h) | h
      · exact .inl (.inl (by rw [hnames]; exact h))
      · exact .inl (.inr (hext n h))
      · exact .inr h
    exact hS.alias a (hsub a ha) b (hsub b hb) x hxa hxb (hfunc a hpa) (hfunc b hpb)

/-! ## The guarded source run -/

/-- **The guarded run**: a per-function run of `f` under the linked environment from a state all
of whose whole-program successors are good returns or traps as under the guarded environment
(every callee is entered at a good state: the whole program enters it there). -/
theorem guard_run {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M : Nat) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd (linkEnvN P B M) P B syms) :
    ∀ (n : Nat) (s : State), UInv P f syms s → GoodFrom B P G syms s →
      (∀ v m, Clif.runLoop (linkEnvN P B M) P.bare n s = .returned v m →
        Clif.runLoop (guardEnv B P G syms M) P.bare n s = .returned v m) ∧
      (∀ c, Clif.runLoop (linkEnvN P B M) P.bare n s = .trapped c →
        Clif.runLoop (guardEnv B P G syms M) P.bare n s = .trapped c) := by
  have hU := unlink_linkN (B := B) hF M
  have hA := agree_guard B P G syms M
  intro n
  induction n with
  | zero => exact fun _ _ _ => ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | succ n ih =>
  intro s hI hG
  rw [runLoop_succ', runLoop_succ']
  -- the next state after a per-function step that continues
  have cont : ∀ s1, step (linkEnvN P B M) P.bare s = .next s1 →
      step (guardEnv B P G syms M) P.bare s = .next s1 →
      (∀ v m, afterStep (linkEnvN P B M) P.bare n (.next s1) = .returned v m →
        afterStep (guardEnv B P G syms M) P.bare n (.next s1) = .returned v m) ∧
      (∀ c, afterStep (linkEnvN P B M) P.bare n (.next s1) = .trapped c →
        afterStep (guardEnv B P G syms M) P.bare n (.next s1) = .trapped c) := by
    intro s1 h1 _
    obtain ⟨k, hk⟩ := unlink_next hU hf hio hI h1
    exact ih s1 (hI.next hU hf hio h1) (hG.of_reach hk.sreach)
  rcases unlink_step hU hf hio hI.callers hI.frame hI.syms with
    ⟨heq, -, -, -⟩ | ⟨h, hhP, vals, c, hW, hCL⟩ | hS
  · rw [heq _ hA]
    cases hst : step (linkEnvN P B M) P.bare s with
    | next s1 => exact cont s1 hst (by rw [heq _ hA, hst])
    | done v m => exact ⟨fun _ _ h => h, fun _ h => h⟩
    | trapped c => exact ⟨fun _ _ h => h, fun _ h => h⟩
    | stuck m => exact ⟨fun _ _ h => h, fun _ h => h⟩
  · have hp := func?_name hF.nd hhP
    have CE := hCL _ (EnvAgree.refl _ _) _ (linkEnvN_some' hp)
    have CG := hCL _ hA _ (guardEnv_some (G := G) (syms := syms) (M := M) hp)
    -- the callee is entered at a good state
    have hgood : GoodCall B P G syms h vals s.mem := by
      intro fr' mem' hent s' hs'
      have hW' : step B P s = .next ((⟨fr', [], mem'⟩ : State).below [c]) := by rw [hW, hent]; rfl
      have := hG (s'.below [c]) (.step hW' (hs'.belowK [c]))
      exact ⟨this.1, memTrapFree_below [c] this.2.1, this.2.2⟩
    have heqF : guardFun B P G syms M h h.name vals s.mem = linkFun B P M h.name vals s.mem :=
      guardFun_good hgood
    rw [heqF] at CG
    cases hst : step (linkEnvN P B M) P.bare s with
    | next s1 =>
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, hty, hr⟩ | ⟨t, ho, hr⟩
      · cases hm
      · have hG2 := CG.1 rv m2 ho hty s1 hr.symm
        rw [hG2]
        exact cont s1 hst hG2
      · cases hr
    | trapped t =>
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, hty, hr⟩ | ⟨t', ho, hr⟩
      · cases hm
      · exact absurd hr.symm resumeStep_ne_trapped
      · cases hr
        rw [CG.2.1 t ho]
        exact ⟨fun _ _ h => h, fun _ h => h⟩
    | done v m =>
      refine ⟨fun _ _ _ => ?_, fun _ h => (by cases h)⟩
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, -, -, hr⟩ | ⟨t', -, hr⟩
      · cases hm
      · exact absurd hr.symm resumeStep_ne_done
      · cases hr
    | stuck m => exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  · obtain ⟨msg, hm⟩ := hS _ (EnvAgree.refl _ _)
    rw [hm]
    exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

/-- The per-function run under the guarded environment from a good state traps at no load or
store (its states are whole-program states). -/
theorem noMemTrap_guard {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M : Nat) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd (guardEnv B P G syms M) P B syms) {s : State}
    (hI : UInv P f syms s) (hG : GoodFrom B P G syms s) :
    NoMemTrap (guardEnv B P G syms M) P.bare s := by
  intro t ht c st rest htr hb
  obtain ⟨k, hk⟩ := ht.steps
  obtain ⟨k', hk'⟩ := unlink_steps (unlink_guard hF M) hf hio hI hk
  have hT := (hG t hk'.sreach).2.1
  have hloc : ∀ (hnc : ∀ fn args, st.inst ≠ .call fn args)
      (hnci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args),
      step (guardEnv B P G syms M) P.bare t = step B P t := fun hnc hnci => by
    rw [step_inst _ _ t st rest hb hnc hnci, step_inst _ _ t st rest hb hnc hnci]
  refine ⟨fun op ty fl a o hi => ?_, fun op ty fl x a o hi => ?_⟩
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).1 op ty fl a o hi
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).2 op ty fl x a o hi

/-! ## Functions without `i128`: the same code under related environments -/

/-- The extern `name` of `E` called with values of the signature `sig` (without `i128`) returns
or traps as `E'`'s. -/
def SameAt (E E' : Env) (name : String) (sig : Signature) : Prop :=
  ∀ hs, E.extern name = some hs → ∃ hs', E'.extern name = some hs' ∧ ∀ vals m,
    vals.map (·.ty) = AbiParam.tys sig.params →
    (∀ rv m', hs vals m = .returned rv m' → rv.map (·.ty) = AbiParam.tys sig.returns →
      hs' vals m = .returned rv m') ∧
    (∀ c, hs vals m = .trapped c → hs' vals m = .trapped c)

/-- One step of a function under related environments (its declared externs `SameAt`, its
indirect calls `CallIndRel`): the same step unless the source is stuck. -/
theorem ident_step {E E' : Env} {P P' : Program} {f : Function}
    (hext : ∀ fn e, f.extern? fn = some e → SameAt E E' e.name e.sig)
    (hind : ∀ i d, f.sigDecls.lookup i = some d → CallIndRel E E' P.bare P'.bare d)
    (hfree : LinkFree f) {s : State} (hI : LFrame (P.only f) s.frame) (hff : s.frame.func = f) :
    (∀ s1, step E P.bare s = .next s1 → step E' P'.bare s = .next s1) ∧
    (∀ v m, step E P.bare s = .done v m → step E' P'.bare s = .done v m) ∧
    (∀ c, step E P.bare s = .trapped c → step E' P'.bare s = .trapped c) := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hfree
  -- the same result unless stuck
  have keep : ∀ r r' : StepResult, ((∀ msg, r ≠ .stuck msg) → r' = r) →
      (∀ s1, r = .next s1 → r' = .next s1) ∧ (∀ v m, r = .done v m → r' = .done v m) ∧
      (∀ c, r = .trapped c → r' = .trapped c) := fun r r' h =>
    ⟨fun s1 h1 => by rw [h (by rw [h1]; exact fun _ e => by cases e), h1],
     fun v m h1 => by rw [h (by rw [h1]; exact fun _ e => by cases e), h1],
     fun c h1 => by rw [h (by rw [h1]; exact fun _ e => by cases e), h1]⟩
  have call : ∀ (t : State) rest rs fn ext vals, t.frame.func = f → f.extern? fn = some ext →
      vals.map (·.ty) = AbiParam.tys ext.sig.params →
      (∀ msg, Opt.callCont E P.bare t rest rs ext vals ≠ .stuck msg) →
        Opt.callCont E' P'.bare t rest rs ext vals = Opt.callCont E P.bare t rest rs ext vals := by
    intro t rest rs fn ext vals _ hfe hv hns
    simp only [Opt.callCont, Program.bare_func?] at hns ⊢
    cases he : E.extern ext.name with
    | none => simp only [he] at hns; exact absurd rfl (hns _)
    | some hs =>
      obtain ⟨hs', he', hrel⟩ := hext fn ext hfe hs he
      simp only [he, he'] at hns ⊢
      cases ho : hs vals t.mem with
      | returned rv m' =>
        simp only [ho] at hns
        cases hb : (rv.map (·.ty) == AbiParam.tys ext.sig.returns) with
        | true => simp only [(hrel vals t.mem hv).1 rv m' ho (by simpa using hb)]
        | false => simp only [hb] at hns; exact absurd rfl (hns _)
      | trapped c => simp only [(hrel vals t.mem hv).2 c ho]
      | stuck m => simp only [ho] at hns; exact absurd rfl (hns _)
      | outOfFuel => simp only [ho] at hns; exact absurd rfl (hns _)
  have ind : ∀ (t : State) rest rs sig d a v, t.frame.func.sigDecls.lookup sig = some d →
      t.frame.func = f → (∀ msg, indCont E P.bare t rest rs sig d a v ≠ .stuck msg) →
        indCont E' P'.bare t rest rs sig d a v = indCont E P.bare t rest rs sig d a v := by
    intro t rest rs sig d a v hd htf hns
    have hrel := hind sig d (by rw [← htf]; exact hd)
    have e1 : indCont E P.bare t rest rs sig d a v =
        StepResult.ofRes (callExternAt E P.bare t.mem d a v) fun (rv, m') =>
          continueWith t rest rs rv m' := rfl
    have e2 : indCont E' P'.bare t rest rs sig d a v =
        StepResult.ofRes (callExternAt E' P'.bare t.mem d a v) fun (rv, m') =>
          continueWith t rest rs rv m' := rfl
    rw [e1] at hns ⊢
    rw [e2]
    cases hx : callExternAt E P.bare t.mem d a v with
    | ok r => rw [(hrel t.mem a v).1 r hx]
    | trap c => rw [(hrel t.mem a v).2 c hx]
    | stuck m => rw [hx] at hns; exact absurd rfl (hns _)
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try E P.bare s hb ht, step_try E' P'.bare s hb ht]
    refine keep _ _ fun hns => ?_
    cases h1 : tryPre s.frame fn et with
    | trap c => rfl
    | stuck m => rfl
    | ok nbbc =>
    obtain ⟨n, b, bc⟩ := nbbc
    rw [h1] at hns
    simp only [StepResult.ofRes_ok] at hns ⊢
    cases h2 : Opt.callArgs (tryState s bc).frame fn args with
    | trap c => rfl
    | stuck m => rfl
    | ok ev =>
    obtain ⟨ext, vals⟩ := ev
    rw [h2] at hns
    simp only [StepResult.ofRes_ok] at hns ⊢
    have hfe : f.extern? fn = some ext := by
      have := Opt.callArgs_extern h2; rw [← hff]; exact this
    have hv : vals.map (·.ty) = AbiParam.tys ext.sig.params := by
      simp only [Opt.callArgs, checkTys, Opt.Res.bind_eq_ok, Opt.Res.check_eq_ok, beq_iff_eq,
        Opt.Res.pure_eq_ok, Opt.Res.ofOption_eq_ok] at h2
      obtain ⟨e, -, vs, -, -, hck, he⟩ := h2
      cases he; exact hck
    exact call _ [] _ fn ext vals hff hfe hv hns
  · rw [step_tryInd E P.bare s hb ht, step_tryInd E' P'.bare s hb ht]
    refine keep _ _ fun hns => ?_
    cases h1 : tryIndPre s.frame et with
    | trap c => rfl
    | stuck m => rfl
    | ok nbbc =>
    obtain ⟨n, b, bc⟩ := nbbc
    rw [h1] at hns
    simp only [StepResult.ofRes_ok] at hns ⊢
    cases h2 : indPre (tryState s bc).frame et.sig callee args with
    | trap c => rfl
    | stuck m => rfl
    | ok dav =>
    obtain ⟨d, a, v⟩ := dav
    rw [h2] at hns
    simp only [StepResult.ofRes_ok] at hns ⊢
    exact ind _ [] _ et.sig d a v (indPre_lookup h2) hff hns
  · rw [step_ind E P.bare s hb hi, step_ind E' P'.bare s hb hi]
    refine keep _ _ fun hns => ?_
    cases h1 : indPre s.frame sig callee args with
    | trap c => rfl
    | stuck m => rfl
    | ok dav =>
    obtain ⟨d, a, v⟩ := dav
    rw [h1] at hns
    simp only [StepResult.ofRes_ok] at hns ⊢
    exact ind s rest st.results sig d a v (indPre_lookup h1) hff hns
  · rw [Opt.step_eq_lift E P.bare s hci, Opt.step_eq_lift E' P'.bare s hci]
    refine keep _ _ fun hns => ?_
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 => rfl
    | ret vals => rfl
    | trap c => rfl
    | stuck m => rfl
    | tail ext vals => exact absurd hl (lstep_ne_tail hPf hI)
    | call ext vals rs rest =>
      rw [hl] at hns
      obtain ⟨st, fn, args, hb, -, -, hca⟩ := Opt.lstep_call_inv hl
      have hfe : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hca
      have hv : vals.map (·.ty) = AbiParam.tys ext.sig.params := by
        simp only [Opt.callArgs, checkTys, Opt.Res.bind_eq_ok, Opt.Res.check_eq_ok, beq_iff_eq,
          Opt.Res.pure_eq_ok, Opt.Res.ofOption_eq_ok] at hca
        obtain ⟨e, -, vs, -, -, hck, he⟩ := hca
        cases he; exact hck
      exact call s rest rs fn ext vals hff hfe hv hns

/-- **Runs of a function under related environments**: a return or trap of the source is the
target's. -/
theorem ident_run {E E' : Env} {P P' : Program} {f : Function}
    (hext : ∀ fn e, f.extern? fn = some e → SameAt E E' e.name e.sig)
    (hind : ∀ i d, f.sigDecls.lookup i = some d → CallIndRel E E' P.bare P'.bare d)
    (hfree : LinkFree f) :
    ∀ (n : Nat) (s : State), s.callers = [] → LFrame (P.only f) s.frame →
      (∀ v m, Clif.runLoop E P.bare n s = .returned v m → Clif.runLoop E' P'.bare n s = .returned v m) ∧
      (∀ c, Clif.runLoop E P.bare n s = .trapped c → Clif.runLoop E' P'.bare n s = .trapped c) := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hfree
  intro n
  induction n with
  | zero => exact fun _ _ _ => ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | succ n ih =>
  intro s hc hI
  have hff : s.frame.func = f := by
    have := hI.1
    simpa [Program.only] using this
  obtain ⟨hn, hd, ht⟩ := ident_step hext hind hfree hI hff
  rw [runLoop_succ', runLoop_succ']
  cases hst : step E P.bare s with
  | next s1 =>
    rw [hn s1 hst]
    have hLI : LInv (P.only f) s := ⟨hI, by rw [hc]; exact fun _ h => nomatch h⟩
    exact ih s1 (step_bare_callers hPf hI hc hst)
      (step_next_linv hPf hLI hst (fun _ h => nomatch h)).1.1
  | done v m => rw [hd v m hst]; exact ⟨fun _ _ h => h, fun _ h => h⟩
  | trapped c => rw [ht c hst]; exact ⟨fun _ _ h => h, fun _ h => h⟩
  | stuck m => exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

/-! ## The source domain of a program -/

/-- **The source domain of a program `P` over the base environment `B`** (link-time symbols
`syms`): every function in `legalOkB` (identity, or `Pre` and a successful legalisation),
distinct names, no `return_call` (in `P` and its legalisation), declarations of the program's
functions with their signatures (in `P` and its legalisation), no function named like a
`__*ti3` helper; where a function mentions `i128`, the base environment's contracts (`HelperOk`:
the helpers divide; `ExtLegal`: an extern called with split arguments returns split results;
`EnvKeepsBounded`); where the legalised program has indirect calls, `IndScope` and no signature
known to `B`. -/
structure ProgCtx (P : Program) (B : Env) (syms : String → Option Nat) : Prop where
  ok : ∀ f ∈ P.funcs, legalOkB f = true
  nd : (P.funcs.map (·.name)).Nodup
  free : ∀ f ∈ P.funcs, LinkFree f
  free' : ∀ f ∈ P.funcs, LinkFree (legalize f)
  decl : ∀ g ∈ P.funcs, ∀ fn e, g.extern? fn = some e → ∀ h, P.func? e.name = some h → h.sig = e.sig
  decl' : ∀ g ∈ (legalProg P).funcs, ∀ fn e, g.extern? fn = some e → ∀ h,
    (legalProg P).func? e.name = some h → h.sig = e.sig
  helpers : ∀ op, P.func? (divHelper op) = none
  base : (∃ f ∈ P.funcs, mentions128 f = true) → HelperOk B ∧ ExtLegal B ∧ EnvKeepsBounded B
  ind : SomeInd (legalProg P) → IndScope (legalProg P) B syms ∧ ∀ n, B.sigOf n = none

theorem find?_legalize : ∀ {l : List Function} (n : String),
    (∀ f ∈ l, (legalize f).name = f.name) →
    (l.map legalize).find? (·.name == n) = (l.find? (·.name == n)).map legalize
  | [], _, _ => rfl
  | f :: l, n, h => by
    simp only [List.map_cons, List.find?_cons, h f (List.mem_cons_self ..)]
    cases (f.name == n) with
    | true => rfl
    | false => exact find?_legalize n fun g hg => h g (List.mem_cons_of_mem _ hg)

namespace ProgCtx

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtx P B syms)
include hC

theorem names : (legalProg P).funcs.map (·.name) = P.funcs.map (·.name) := by
  simp only [legalProg_funcs, List.map_map]
  exact List.map_congr_left fun f hf => (legalFacts (hC.ok f hf)).name

theorem facts : ProgFacts P := ⟨hC.nd, hC.free, hC.decl⟩

theorem facts' : ProgFacts (legalProg P) :=
  ⟨by rw [hC.names]; exact hC.nd, fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact hC.free' f hf, hC.decl'⟩

theorem func? (n : String) : (legalProg P).func? n = (P.func? n).map legalize :=
  _root_.E2E.LegalProgram.find?_legalize n fun f hf => (legalFacts (hC.ok f hf)).name

theorem func?_some {n : String} {h : Function} (hp : P.func? n = some h) :
    (legalProg P).func? n = some (legalize h) := by
  rw [hC.func? n, hp]; rfl

theorem func?_none {n : String} (hp : P.func? n = none) : (legalProg P).func? n = none := by
  rw [hC.func? n, hp]; rfl

theorem externNames {n : String} (hn : n ∈ P.externNames) : n ∈ (legalProg P).externNames := by
  simp only [Program.externNames, List.mem_flatMap, legalProg_funcs, List.mem_map] at hn ⊢
  obtain ⟨f, hf, hn⟩ := hn
  obtain ⟨hn', heq, -⟩ := (legalFacts (hC.ok f hf)).names
  refine ⟨legalize f, ⟨f, hf, rfl⟩, ?_⟩
  have hm : n ∈ (legalize f).externs.map (·.2.name) := by
    rw [heq]; exact List.mem_append_left _ (List.mem_map.mpr hn)
  exact List.mem_map.mp hm

theorem someInd {f : Function} (hf : f ∈ P.funcs) (hn : ¬ IndFree f) : SomeInd (legalProg P) :=
  ⟨legalize f, List.mem_map_of_mem hf, (legalFacts (hC.ok f hf)).ind hn⟩

theorem indSrc (hI : SomeInd (legalProg P)) : IndScope P B syms :=
  indScope_src (hC.ind hI).1 hC.names (fun _ h => hC.externNames h) fun _ h => hC.func?_none h

end ProgCtx

/-! ## The induction -/

/-- **The refinement at fuel `M`**: a whole-program run of a function `h` of `P` from an entry
all of whose whole-program successors are good that returns or traps within `M` steps is matched
by the whole-program run of `legalize h` in `legalProg P` from the entry with the ABI-split
arguments. -/
def Refines (B : Env) (P : Program) (syms : String → Option Nat) (M : Nat) : Prop :=
  ∀ h ∈ P.funcs, ∀ vals vals' m fr m1 fr', enterFunc h vals m = .ok (fr, m1) →
    enterFunc (legalize h) vals' m = .ok (fr', m1) →
    ExpRel ((groups h.sig.params).getD []) vals vals' →
    GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ →
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c)

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtx P B syms)
  {M : Nat} (ih : Refines B P syms M)
include hC ih

/-- A callee run of the guarded environment and the target's: related by the induction
hypothesis. -/
theorem prog_call {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFun B P (SomeInd (legalProg P)) syms M h2 n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFun B (legalProg P) n vals' m = .returned rv' m') ∧
    (∀ c, guardFun B P (SomeInd (legalProg P)) syms M h2 n vals m = .trapped c →
      tgtFun B (legalProg P) n vals' m = .trapped c) := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.func?_some hp
  have key : ∀ o, guardFun B P (SomeInd (legalProg P)) syms M h2 h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ ∧
        Clif.runLoop B P M ⟨fr, [], m1⟩ = o := by
    intro o ho hs
    obtain ⟨hgood, hl⟩ := guardFun_cases ho hs
    unfold linkFun at hl
    cases hi : initState P h2.name vals m with
    | ok s =>
      rw [hi] at hl
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legal (hC.ok h2 hh2) he hexp
      exact ⟨fr, m1, fr', he, he', hgood fr m1 he, hl⟩
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at hl; exact absurd hl.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = o → o ≠ .outOfFuel →
      tgtFun B (legalProg P) h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho
    unfold tgtFun
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    show runLim B (legalProg P) ⟨fr', [], m1⟩ = o
    rw [runLim_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h)⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)

end Induction

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtx P B syms)
  {M : Nat} (ih : Refines B P syms M)
include hC ih

/-- The source's guarded environment and the target's are related at the declaration `n` of a
function of `P` (with its signature, `ProgCtx.decl`). -/
theorem extRel_prog {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) n sig := by
  intro hs he
  rw [guardEnv_some hp] at he
  cases he
  refine ⟨_, tgtEnv_some (hC.func?_some hp), fun gs rg hgs hrg vals vals' m hty hexp => ?_⟩
  have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
    rw [hsig, hgs]; exact hexp
  obtain ⟨h1, h2'⟩ := prog_call hC ih hp hexp'
  refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
  obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
  refine ⟨rv', ht, ?_⟩
  rw [hsig, hrg] at hrel
  exact hrel

/-- At a declaration without `i128` (of a function of `P`, with its signature, or of the base
environment), the two environments return the same values. -/
theorem sameAt_link {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAt (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) n sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnv_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnv_some (hC.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2'⟩ := prog_call hC ih hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnv_none hpn] at he
    exact ⟨hs, by rw [tgtEnv_none (hC.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho⟩⟩

/-- An indirect call with a call-site signature without `i128`: the two environments resolve the
address to the same name and return the same values. -/
theorem callIndRel_link {d : Signature} (hd : sig128 d = false) :
    CallIndRel (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) P.bare
      (legalProg P).bare d := by
  intro mem a vals
  have hnames : ((guardEnv B P (SomeInd (legalProg P)) syms M).names ++ P.bare.externNames) =
      ((tgtEnv B P (legalProg P)).names ++ (legalProg P).bare.externNames) := by
    simp [guardEnv, tgtEnv, linkEnvN_names]
  -- a function of `P` reached with a signature without `i128` has none either
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnv B P (SomeInd (legalProg P)) syms M).sigOf n).all d.abiMatch = true →
      ((tgtEnv B P (legalProg P)).sigOf n).all d.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys d.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : d.abiMatch h2.sig = true := by
      simpa [guardEnv, linkEnvN_sigOf, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFacts (hC.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnv, hC.func?_some hpn, hl2, hs']
  have hexpOf : ∀ n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys d.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys d.params → ExpRel ((groups h2.sig.params).getD []) vals vals := by
    intro n h2 _ h2p htp hv
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params h2p)
    rw [hgs, Option.getD_some]
    refine expRel_refl_plain hG (sig128_params h2p) ?_
    have := congrArg List.length (hv.trans htp)
    simpa [AbiParam.tys] using this
  constructor
  · intro r hr
    obtain ⟨n, g, h1, hg, hs, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnv_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1', -⟩ := prog_call hC ih hpn (hexpOf n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1' rv m' ho
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1, tgtEnv_some (hC.func?_some hpn), hs', hv, rv, m',
        ht, hrt, rfl⟩
    | none =>
      rw [guardEnv_none hpn] at hg
      have hsN : (tgtEnv B P (legalProg P)).sigOf n = none := by
        simp [tgtEnv, hC.func?_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1, by rw [tgtEnv_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, rv, m', ho, hrt, rfl⟩
  · intro c hr
    obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnv_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2'⟩ := prog_call hC ih hpn (hexpOf n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1, tgtEnv_some (hC.func?_some hpn), hs', hv,
        h2' c ho⟩
    | none =>
      rw [guardEnv_none hpn] at hg
      have hsN : (tgtEnv B P (legalProg P)).sigOf n = none := by
        simp [tgtEnv, hC.func?_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1, by rw [tgtEnv_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, ho⟩

end Induction

theorem LInv.steps {env : Env} {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) :
    ∀ {k : Nat} {s s1 : State}, StepsTo env P k s s1 → LInv P s → LInv P s1
  | 0, s, s1, h, hI => by simp only [StepsTo] at h; rw [h]; exact hI
  | k + 1, s, s1, ⟨s', hs, h⟩, hI => LInv.steps hP h (step_next_linv hP hI hs).1

/-- The guarded environment keeps valid ranges below `2^64` (a callee's states are good). -/
theorem keep_guard {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}
    (hF : ProgFacts P) (hb : EnvKeepsBounded B) : EnvKeepsBounded (guardEnv B P G syms M) := by
  intro name g hg vals m rv m' hr hM
  cases hpn : P.func? name with
  | none => rw [guardEnv_none hpn] at hg; exact hb name g hg vals m rv m' hr hM
  | some h2 =>
    rw [guardEnv_some hpn] at hg
    cases hg
    obtain ⟨hh2, rfl⟩ := Program.func?_some hpn
    obtain ⟨hgood, hl⟩ := guardFun_cases hr (fun _ h => by cases h)
    obtain ⟨fr', mem', he, N, hN⟩ := (linkFun_prog hpn vals m).1 rv m' hl
    obtain ⟨k, t, hst, hdone⟩ := runLoop_returned_steps N _ rv m' hN
    have hGt := hgood fr' mem' he t hst.sreach
    have hLt : LInv P t := LInv.steps hF.free hst ⟨LFrame.enterFunc hh2 he, fun _ h => nomatch h⟩
    exact fun a n hv => hGt.1 a n (step_done_valid hF.free hLt hdone a n hv)

/-! ## Entries and the refinement -/

theorem entry_mem {f : Function} {b : Block} (h : f.entry? = some b) : b ∈ f.blocks := by
  simp only [Function.entry?] at h
  cases hb : f.blocks with
  | nil => rw [hb] at h; cases h
  | cons x xs =>
    rw [hb] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    rw [h]
    exact List.mem_cons_self ..

/-- **Entry frames** of `h` on `args` and of its legalisation on the ABI-split `args'`, with the
same slots (`Clif.enterFunc` without the slot addresses, as `E2E.ClifEntry`). -/
structure EntryRel (h : Function) (args args' : List Val) (fr fr' : Frame) : Prop where
  func : fr.func = h
  func' : fr'.func = legalize h
  entry : ∃ b, h.entry? = some b ∧ fr.body = b.body ∧ fr.term = b.term ∧
    b.params.map (·.2) = args.map (·.ty) ∧ Regs.empty.setMany (b.params.map (·.1)) args = some fr.regs
  entry' : ∃ b', (legalize h).entry? = some b' ∧ fr'.body = b'.body ∧ fr'.term = b'.term ∧
    Regs.empty.setMany (b'.params.map (·.1)) args' = some fr'.regs
  slots : fr'.slots = fr.slots
  exp : ExpRel ((groups h.sig.params).getD []) args args'

theorem EntryRel.lframe {h : Function} {args args' : List Val} {fr fr' : Frame}
    (hE : EntryRel h args args' fr fr') {Q : Program} (hh : h ∈ Q.funcs) : LFrame Q fr := by
  obtain ⟨b, hb, h2, h3, -, -⟩ := hE.entry
  refine ⟨by rw [hE.func]; exact hh, .inl ⟨b, by rw [hE.func]; exact entry_mem hb, ?_, h3⟩⟩
  rw [h2]; exact List.suffix_refl _

theorem EntryRel.lframe' {h : Function} {args args' : List Val} {fr fr' : Frame}
    (hE : EntryRel h args args' fr fr') {Q : Program} (hh : legalize h ∈ Q.funcs) : LFrame Q fr' := by
  obtain ⟨b, hb, h2, h3, -⟩ := hE.entry'
  refine ⟨by rw [hE.func']; exact hh, .inl ⟨b, by rw [hE.func']; exact entry_mem hb, ?_, h3⟩⟩
  rw [h2]; exact List.suffix_refl _

theorem EntryRel.of_enter {h : Function} {vals vals' : List Val} {m m1 : Mem} {fr fr' : Frame}
    (hl : (legalize h).name = h.name ∧ (legalize h).slots = h.slots)
    (he : enterFunc h vals m = .ok (fr, m1)) (he' : enterFunc (legalize h) vals' m = .ok (fr', m1))
    (hexp : ExpRel ((groups h.sig.params).getD []) vals vals') : EntryRel h vals vals' fr fr' := by
  obtain ⟨b, regs, hb, -, hbt, hr, hsl, hfr⟩ := Opt.enterFunc_ok he
  obtain ⟨b', regs', hb', -, -, hr', hsl', hfr'⟩ := Opt.enterFunc_ok he'
  refine ⟨by rw [hfr], by rw [hfr'], ⟨b, hb, by rw [hfr], by rw [hfr], hbt.symm, by rw [hfr]; exact hr⟩,
    ⟨b', hb', by rw [hfr'], by rw [hfr'], by rw [hfr']; exact hr'⟩, ?_, hexp⟩
  have e := Opt.enterSlots_congr hl.1 hl.2 m
  rw [hsl', hsl] at e
  simp only [Prod.mk.injEq] at e
  exact e.1

/-- **The refinement of one activation at fuel `M + 1`** from entry frames (`EntryRel`, any slot
addresses and memory), the callees related at fuel `M` (`Refines`). -/
theorem root_refines {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) {M : Nat} (ih : Refines B P syms M) {h : Function} (hh : h ∈ P.funcs)
    {args args' : List Val} {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) :
    (∀ rv m2, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) := by
  have hF := hC.facts
  have hF' := hC.facts'
  have hfacts := legalFacts (hC.ok h hh)
  have hhP' : legalize h ∈ (legalProg P).funcs := List.mem_map_of_mem hh
  have hio : ¬ IndFree h → SomeInd (legalProg P) := fun hn => hC.someInd hh hn
  have hLe : LInv P ⟨fr, [], m1⟩ := ⟨hE.lframe hh, fun _ h => nomatch h⟩
  have hLeh : LInv (P.only h) ⟨fr, [], m1⟩ :=
    ⟨hE.lframe (by simp [Program.only]), fun _ h => nomatch h⟩
  have hsym : ¬ IndFree h → m1.symbols = syms := fun hn => (hG _ (.refl _)).2.2 (hio hn)
  have hUI : UInv P h syms ⟨fr, [], m1⟩ := ⟨rfl, hLeh.1, hsym⟩
  have hioE : ¬ IndFree h → UnlinkInd (linkEnvN P B M) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  have hioG : ¬ IndFree h →
      UnlinkInd (guardEnv B P (SomeInd (legalProg P)) syms M) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  -- the source run is a per-function run under the guarded linked environment
  have hlink : ∀ o, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = o → (∀ msg, o ≠ .stuck msg) →
      o ≠ .outOfFuel → ∃ n, Clif.runLoop (linkEnvN P B M) P.bare n ⟨fr, [], m1⟩ = o := by
    intro o ho hs hof
    obtain ⟨n, hn⟩ := runLoop_linkN (P := P) (base := B) (f := h) (syms := syms) M hC.nd hh
      hC.free (fun hn => hC.indSrc (hio hn)) (E := linkEnvN P B M) rfl rfl (fun _ _ => rfl)
      (fun _ _ _ => rfl) (M + 1) ⟨fr, [], m1⟩ (Nat.le_refl _) hLe hLeh hsym
      (by rw [ho]; exact hs) (by rw [ho]; exact hof)
    exact ⟨n, hn.trans ho⟩
  have hguard := guard_run (G := SomeInd (legalProg P)) hF M hh hioE
  -- the target's per-function run is a whole-program run
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) → UnlinkInd (tgtEnv B P (legalProg P)) (legalProg P) B syms :=
    fun hn => unlinkInd_tgt (hC.ind ⟨_, hhP', hn⟩).1 (hC.ind ⟨_, hhP', hn⟩).2 hC.names
      (fun _ h => hC.externNames h)
  have hwhole := fun n => unlink_run (unlink_tgt (B := B) (P := P) hF') hhP' hioT (n := n) hUIt
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, Clif.runLoop (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨fr, [], m1⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, Clif.runLoop (tgtEnv B P (legalProg P)) (legalProg P).bare k ⟨fr', [], m1⟩ =
            .returned rv' m2) ∧
      (∀ n c, Clif.runLoop (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨fr, [], m1⟩ = .trapped c →
        ∃ k, Clif.runLoop (tgtEnv B P (legalProg P)) (legalProg P).bare k ⟨fr', [], m1⟩ =
          .trapped c) := by
    obtain ⟨b, hb, h2, h3, h4, h5⟩ := hE.entry
    obtain ⟨b', hb', h2', h3', h5'⟩ := hE.entry'
    rcases Complete.legalOkB_cases (hC.ok h hh) with ⟨hm, -, hl⟩ | ⟨hp, cert, hc⟩
    · -- the identity: the same code, related environments
      obtain ⟨hs, hes, hds⟩ := not_mentions hm
      obtain ⟨gs, hgs, hGs⟩ := groups_plain (sig128_params hs)
      have hexp := hE.exp
      rw [hgs, Option.getD_some] at hexp
      have hvv : args' = args := expRel_val hGs (sig128_params hs) hexp
      have hfe : fr' = fr := by
        rw [hl] at hb'
        rw [hb] at hb'
        cases hb'
        obtain ⟨func, regs, slots, body, term⟩ := fr
        obtain ⟨func', regs', slots', body', term'⟩ := fr'
        have e1 : func' = func := by
          have := hE.func'; have := hE.func; simp_all
        simp only at h2 h3 h5 h2' h3' h5' e1
        rw [hvv, h5] at h5'
        cases h5'
        have e2 := hE.slots
        simp only at e2
        subst e1 e2
        rw [h2, h2', h3, h3']
      subst hfe
      have hrun := ident_run (E := guardEnv B P (SomeInd (legalProg P)) syms M)
        (E' := tgtEnv B P (legalProg P)) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAt_link hC ih (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.decl h hh fn ex hfe h2 hpn))
        (fun i d hd => callIndRel_link hC ih (by
          obtain ⟨i', hmem⟩ := lookup_mem hd
          exact hds _ hmem))
        (hC.free h hh)
      refine ⟨fun n rv m2 hr hty => ⟨rv, ?_, n, (hrun n _ rfl hLeh.1).1 rv m2 hr⟩,
        fun n c hr => ⟨n, (hrun n _ rfl hLeh.1).2 c hr⟩⟩
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      rw [hrg, Option.getD_some]
      refine expRel_refl_plain hR (sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [AbiParam.tys] using this
    · -- a legalisation: `legalize_refines2` with the two environments
      have hbase := hC.base ⟨h, hh, hp.mentions⟩
      have hE2 : EnvOk2 (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P))
          ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { src := fun _ _ _ => rfl
          tgt := fun _ _ _ => rfl
          helper := fun op => by
            obtain ⟨hf, hB, hsem⟩ := hbase.1 op
            exact ⟨hf, by rw [tgtEnv_none (hC.func?_none (hC.helpers op))]; exact hB, hsem⟩
          ext := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact extRel_prog hC ih hpn (hC.decl h hh fn ex hfe h2 hpn)
            | none =>
              intro hs he
              rw [guardEnv_none hpn] at he
              obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
              exact ⟨h', by rw [tgtEnv_none (hC.func?_none hpn)]; exact hb', hrel⟩
          keep := keep_guard hF hbase.2.2
          ind := fun _ => ⟨rfl, fun sig d hs hd =>
            have hd128 := pre_indSite hp hs hd
            callIndRel2_of_plain hd128 (callIndRel_link hC ih hd128)⟩ }
      have hT := noMemTrap_guard hF M hh hioG hUI hG
      have hI : NoIndInternal (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ => ⟨(fun _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg),
            (fun _ _ _ _ _ _ _ _ g hg => nomatch hg)⟩
      have href := fun n => legalize_refines2 hp hc hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2'
        h3' h5' hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2 c hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG).1 rv m2 hn
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoop_returned_tys hC.free (M + 1) _ rv m2 hLe hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn'' hty
    obtain ⟨k', hk'⟩ := (hwhole k).1 rv' m2 hk
    exact ⟨rv', hrel, k', hk'⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG).2 c hn
    obtain ⟨k, hk⟩ := hact.2 n c hn''
    exact (hwhole k).2 c hk

/-- **The callees are related at every fuel** (by induction on the fuel). -/
theorem prog_refines {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) : ∀ M, Refines B P syms M := by
  intro M
  induction M with
  | zero =>
    intro h _ vals vals' m fr m1 fr' _ _ _ _
    exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M ih =>
    intro h hh vals vals' m fr m1 fr' hent hent' hexp hG
    have hfacts := legalFacts (hC.ok h hh)
    exact root_refines hC ih hh (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG

/-- **Whole-program refinement of the original program** (S3): on the source domain
(`ProgCtx`), a whole-program run of a function `h` of `P` from entry frames (`EntryRel`: the
target's on the ABI-split arguments, the same slots) and memory all of whose whole-program
successors are good (`GoodFrom`) that returns within `M` steps is a return of the legalised
program's run with the results split by `h`'s return groups and the same memory; a trap is the
same trap. -/
theorem legalProg_refines {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) (M : Nat) :
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) := by
  cases M with
  | zero => exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M => exact root_refines hC (prog_refines hC M) hh hE hG

/-! ## Good runs -/

/-- A run that returns never traps on its way: no reachable state traps (deterministic runs). -/
theorem memTrapFree_of_returned {env : Env} {p : Program} :
    ∀ (N : Nat) (s : State) (v : List Val) (m : Mem), Clif.runLoop env p N s = .returned v m →
      ∀ s', SReach env p s s' → MemTrapFree env p s'
  | 0, _, _, _, h, _, _ => by simp at h
  | N + 1, s, v, m, h, s', hr => by
    rw [runLoop_succ'] at h
    cases hr with
    | refl =>
      intro c st rest hs
      rw [hs] at h
      cases h
    | step hs hr' =>
      rw [hs] at h
      exact memTrapFree_of_returned N _ v m h s' hr'

end E2E.LegalProgram
