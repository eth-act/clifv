import FV.E2E.LegalProgram
import FV.E2E.LinkClifRevX
import FV.Opt.Proof.LegalSimX2

/-!
# Whole-program refinement of the original `i128` program, with unwinding (S10f, #233)

`legalProg_refinesX`: S3's `legalProg_refines` (`FV/E2E/LegalProgram.lean`) for the runs with
unwinding (`Clif.runLoopX`). On the source domain with unwinding (`ProgCtxX`: S3's `ProgCtx` of
the environment without unwinding, the unwinding contracts of the base environment `B` where a
function mentions `i128` — `ExtLegalX`, `EnvKeepsAllocsX`, `ExnArityOk` —, `IndScopeX` where the
legalised program has indirect calls, and the handler-edge check `Opt.Legal.exnOk` of every
legalised function), a whole-program run with unwinding of a function `h` of `P` from entry frames
(`EntryRel`) and a memory all of whose whole-program successors are good (`GoodFromX`) that
returns, traps or unwinds within `M` steps is matched by the whole-program run with unwinding of
`legalize h` in `legalProg P`: the results split by `h`'s return groups with the same memory, the
same trap, the same exception with the same memory.

The proof is S3's induction on the fuel, with unwinding:

* the source run is a per-function run of `P.bare` under the guarded linked environment
  (`guardEnvX`: a callee's whole-program run with unwinding, entered only at good states;
  `Clif.runLoopX_linkR`, every callee entered by the source run being entered at a good state);
* each activation: `Opt.Legal.X.check_refinesX2` (two environments, `EnvOkX2`) for a legalised
  function, `identX_run` (the same code under environments agreeing where the source's calls
  end) for an identity one; the two environments related at every callee by the induction
  hypothesis (`prog_callX`);
* the target's per-function run under `tgtEnvX` (a callee's whole-program run with unwinding,
  unbounded) is a whole-program run (`Clif.unlinkX_run`); the source run's states are whole-program
  states (`Clif.unlinkX_reach`), so the source run has no load/store trap where the whole
  program has none.
-/

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128

/-! ## Runs with unwinding: exceptions and memories -/

theorem valid_freeLeave {mem : Mem} {xs : List Nat} {a k : Nat}
    (h : ((mem.free xs).leave).valid a k = true) : mem.valid a k = true := by
  rw [Mem.leave_valid] at h
  simp only [Mem.valid, Mem.free, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨x, ⟨hx, -⟩, hx2⟩ := h
  exact ⟨x, hx, hx2⟩

theorem unwindFrom_valid (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (e' : Exn) (m : Mem), unwindFrom e fr cs ts mem = .unwound e' m →
      ∀ a k, m.valid a k = true → mem.valid a k = true
  | fr, [], _, mem, e', m, h => by
    simp only [unwindFrom, XStepResult.unwound.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun a k hv => valid_freeLeave hv
  | fr, (c, rs) :: cs, t :: ts, mem, e', m, h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r _
      cases r <;> simp [XStepResult.ofRes] at h
    · exact fun a k hv => valid_freeLeave (unwindFrom_valid e c cs ts _ e' m h a k hv)
  | fr, _ :: _, [], mem, e', m, h => by simp [unwindFrom] at h

/-- **A step that unwinds raised its exception at an extern**, whose memory has every valid range
of the step's final memory. -/
theorem stepX_unwound_extern {env : XEnv} {p : Program} {xs : XState} {e : Exn} {m : Mem}
    (h : stepX env p xs = .unwound e m) :
    ∃ n g vals mx, env.extern n = some g ∧ g vals xs.s.mem = .unwound e mx ∧
      ∀ a k, m.valid a k = true → mx.valid a k = true := by
  unfold stepX at h
  split at h
  · rename_i e1 mem1 hr
    obtain ⟨n, g, vals, hg, hgo⟩ := raiseAt_extern hr
    unfold raiseIn at h
    split at h
    · rename_i r _
      cases r <;> simp [XStepResult.ofRes] at h
    · have he := unwindFrom_unwound_exn _ _ _ _ _ _ _ h
      subst he
      exact ⟨n, g, vals, mem1, hg, hgo, unwindFrom_valid _ _ _ _ _ _ _ h⟩
  · cases hstep : step env.toEnv p xs.s <;> rw [hstep] at h <;> simp [liftStep] at h

/-- A run with unwinding that returns or unwinds reaches no state whose step traps. -/
theorem stepX_ne_trapped_of_run {env : XEnv} {p : Program} :
    ∀ (N : Nat) (xs : XState) (o : XOutcome), runLoopX env p N xs = o → (∀ c, o ≠ .trapped c) →
      o ≠ .outOfFuel → ∀ u, ReachesX env p xs u → ∀ c, stepX env p u ≠ .trapped c
  | 0, _, o, h, _, hof, _, _, _, _ => hof (by rw [← h]; rfl)
  | N + 1, xs, o, h, ht, hof, u, hu, c, hc => by
    rw [runLoopX_succ'] at h
    cases hu with
    | refl => rw [hc] at h; exact ht c h.symm
    | next hs hu' =>
      rw [hs] at h
      exact stepX_ne_trapped_of_run N _ o h ht hof u hu' c hc

/-- **A run with unwinding that returns or unwinds has no load/store trap on its way.** -/
theorem memTrapFree_of_runX {env : XEnv} {p : Program} {N : Nat} {xs : XState} {o : XOutcome}
    (h : runLoopX env p N xs = o) (ht : ∀ c, o ≠ .trapped c) (hof : o ≠ .outOfFuel) :
    ∀ u, ReachesX env p xs u → MemTrapFree env.toEnv p u.s := by
  intro u hu c st rest hst hb
  have hne := stepX_ne_trapped_of_run N xs o h ht hof u hu c
  refine ⟨fun op ty fl a o' hi => ?_, fun op ty fl x a o' hi => ?_⟩
  · have hra : raiseAt? env p u.s = none := by simp [raiseAt?, hb, hi]
    exact hne (by simp [stepX, hra, hst, liftStep])
  · have hra : raiseAt? env p u.s = none := by simp [raiseAt?, hb, hi]
    exact hne (by simp [stepX, hra, hst, liftStep])

/-! ## Good states -/

/-- **Good whole-program states with unwinding from `xs`**: valid ranges below `2^64`, no
load/store trap, the link-time symbols `syms` (if `G`). -/
def GoodFromX (B : XEnv) (P : Program) (G : Prop) (syms : String → Option Nat) (xs : XState) :
    Prop :=
  ∀ u, ReachesX B P xs u → MemBounded u.s.mem ∧ MemTrapFree B.toEnv P u.s ∧
    (G → u.s.mem.symbols = syms)

theorem GoodFromX.of_reach {B : XEnv} {P : Program} {G : Prop} {syms : String → Option Nat}
    {xs xs1 : XState} (h : GoodFromX B P G syms xs) (hr : ReachesX B P xs xs1) :
    GoodFromX B P G syms xs1 :=
  fun u hu => h u (hr.trans hu)

/-- A callee entered (below the callers `K`, tables `T`) at a state reached from a good state is
good from its entry. -/
theorem GoodFromX.callee {B : XEnv} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hP : ∀ g ∈ P.funcs, LinkFree g) {s0 t0 : XState} {K : List (Frame × List ValueId)}
    {T : List (Option ExnTable)} (h : GoodFromX B P G syms s0) (hI : XInv P t0)
    (hr : ReachesX B P s0 (t0.below K T)) : GoodFromX B P G syms t0 := by
  intro u hu
  have := h _ (hr.trans (hu.under hP K T hI))
  exact ⟨this.1, memTrapFree_below K this.2.1, this.2.2⟩

/-! ## The environments -/

open Classical in
/-- The callee run of the guarded environment: the whole-program run with unwinding of at most
`M` steps from a good entry. -/
noncomputable def guardRX (B : XEnv) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M : Nat) (t0 : State) : XOutcome :=
  if GoodFromX B P G syms t0.toX then runLoopX B P M t0.toX else .stuck "outside the source run"

/-- **The guarded linked environment with unwinding** of the source program `P`. -/
noncomputable def guardEnvX (B : XEnv) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M : Nat) : XEnv :=
  linkEnvRX P B (guardRX B P G syms M)

/-- **The target's linked environment with unwinding**: a function of the legalised program `P'`
runs its whole-program run with unwinding (unbounded); an address resolves through the source
program's names. -/
noncomputable def tgtEnvX (B : XEnv) (P P' : Program) : XEnv :=
  { linkEnvRX P' B (fun s => runLimX B P' s.toX) with names := P.names ++ B.names }

/-- A function's extern in the guarded environment. -/
noncomputable def guardFunX (B : XEnv) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M : Nat) (n : String) : List Val → Mem → XOutcome := fun vals mem =>
  match initState P n vals mem with
  | .ok s => guardRX B P G syms M s
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-- A function's extern in the target's environment. -/
noncomputable def tgtFunX (B : XEnv) (P' : Program) (n : String) : List Val → Mem → XOutcome :=
  fun vals mem =>
    match initState P' n vals mem with
    | .ok s => runLimX B P' s.toX
    | .trap c => .trapped c
    | .stuck m => .stuck m

section Env
variable {B : XEnv} {P P' : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}

theorem guardEnvX_some {n : String} {h : Function} (hp : P.func? n = some h) :
    (guardEnvX B P G syms M).extern n = some (guardFunX B P G syms M n) := by
  rw [guardEnvX, linkEnvRX_some hp]; rfl

theorem guardEnvX_none {n : String} (hp : P.func? n = none) :
    (guardEnvX B P G syms M).extern n = B.extern n := linkEnvRX_none hp

theorem tgtEnvX_some {n : String} {h : Function} (hp : P'.func? n = some h) :
    (tgtEnvX B P P').extern n = some (tgtFunX B P' n) := by
  show (linkEnvRX P' B _).extern n = _
  rw [linkEnvRX_some hp]; rfl

theorem tgtEnvX_none {n : String} (hp : P'.func? n = none) :
    (tgtEnvX B P P').extern n = B.extern n := linkEnvRX_none hp

theorem toEnv_extern_some {E : XEnv} {n : String} {g : List Val → Mem → XOutcome}
    (h : E.extern n = some g) : E.toEnv.extern n = some fun vals mem => (g vals mem).toOutcome := by
  simp [XEnv.toEnv, h]

theorem toEnv_extern_some_inv {E : XEnv} {n : String} {g : List Val → Mem → Outcome}
    (h : E.toEnv.extern n = some g) :
    ∃ gx, E.extern n = some gx ∧ g = fun vals mem => (gx vals mem).toOutcome := by
  simp only [XEnv.toEnv, Option.map_eq_some_iff] at h
  obtain ⟨gx, hx, rfl⟩ := h
  exact ⟨gx, hx, rfl⟩

theorem toOutcome_returned {o : XOutcome} {rv : List Val} {m : Mem}
    (h : o.toOutcome = .returned rv m) : o = .returned rv m := by
  cases o <;> simp_all [XOutcome.toOutcome]

theorem toOutcome_trapped {o : XOutcome} {c : TrapCode} (h : o.toOutcome = .trapped c) :
    o = .trapped c := by
  cases o <;> simp_all [XOutcome.toOutcome]

/-- The guarded environment unlinks `P` (its callee runs are whole-program runs). -/
theorem unlinkX_guard (hF : ProgFacts P) : UnlinkX (guardEnvX B P G syms M) P B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, guardEnvX_some hp, fun vals mem o ho hs hof => ?_⟩
    unfold guardFunX at ho
    cases hi : initState P h.name vals mem with
    | ok s =>
      obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
      simp only [hi] at ho
      by_cases hgd : GoodFromX B P G syms (State.toX ⟨fr, [], mem'⟩)
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact ⟨fr, mem', he, M, ho⟩
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact absurd ho.symm (hs _)
    | trap c => exact absurd hi (initState_not_trap P h.name vals mem c)
    | stuck msg => rw [hi] at ho; exact absurd ho.symm (hs msg)
  base _ hn := guardEnvX_none hn
  names := ⟨P.externNames ++ B.names, by simp [guardEnvX, Program.names], fun _ h => by
    simpa using h⟩
  sigOf _ := rfl

/-- The target's environment unlinks the legalised program. -/
theorem unlinkX_tgt (hF : ProgFacts P') (hnames : P'.funcs.map (·.name) = P.funcs.map (·.name))
    (hext : ∀ n ∈ P.externNames, n ∈ P'.externNames) : UnlinkX (tgtEnvX B P P') P' B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, tgtEnvX_some hp, fun vals mem o ho hs hof => ?_⟩
    unfold tgtFunX at ho
    cases hi : initState P' h.name vals mem with
    | ok s =>
      obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
      simp only [hi] at ho
      by_cases hex : ∃ n, runLoopX B P' n (State.toX ⟨fr, [], mem'⟩) ≠ .outOfFuel
      · simp only [runLimX, hex, ↓reduceDIte] at ho; exact ⟨fr, mem', he, _, ho⟩
      · simp only [runLimX, hex, ↓reduceDIte] at ho; exact absurd ho.symm hof
    | trap c => exact absurd hi (initState_not_trap P' h.name vals mem c)
    | stuck msg => rw [hi] at ho; exact absurd ho.symm (hs msg)
  base _ hn := tgtEnvX_none hn
  names := ⟨P.externNames ++ B.names, by simp [tgtEnvX, Program.names, hnames], fun n h => by
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (hext n h)
    · exact List.mem_append_right _ h⟩
  sigOf _ := rfl

end Env

/-! ## The source domain with unwinding -/

/-- **The source domain of a program `P` with unwinding** over the base environment `B`: S3's
`ProgCtx` of `B` without unwinding; where a function mentions `i128`, `B`'s contracts for its
unwinding externs (`ExtLegalX`: an extern unwinds alike on the split arguments;
`EnvKeepsAllocsX`; `ExnArityOk`); where the legalised program has indirect calls, `IndScopeX`
(the externs keep the symbols when they unwind too); and the handler-edge check `exnOk` of every
legalisation. -/
structure ProgCtxX (P : Program) (B : XEnv) (syms : String → Option Nat) : Prop where
  ctx : ProgCtx P B.toEnv syms
  baseX : (∃ f ∈ P.funcs, mentions128 f = true) →
    ExtLegalX B ∧ EnvKeepsAllocsX B ∧ ExnArityOk B
  indX : SomeInd (legalProg P) → IndScopeX (legalProg P) B syms
  exn : ∀ f ∈ P.funcs, mentions128 f = true → ∀ g cert, function128Cert f = .ok (g, cert) →
    exnOk f g cert = true

/-- `IndScopeX` of the source program from the legalised one's. -/
theorem indScopeX_src {B : XEnv} {P P' : Program} {syms : String → Option Nat}
    (hS : IndScopeX P' B syms) (hnames : P'.funcs.map (·.name) = P.funcs.map (·.name))
    (hext : ∀ n ∈ P.externNames, n ∈ P'.externNames)
    (hfunc : ∀ n, P.func? n = none → P'.func? n = none) : IndScopeX P B syms where
  keep := hS.keep
  keepU := hS.keepU
  inj := by rw [← hnames]; exact hS.inj
  alias a ha b hb x hxa hxb hpa hpb := by
    have hsub : ∀ n ∈ P.names ++ B.names, n ∈ P'.names ++ B.names := fun n hn => by
      simp only [Program.names, List.mem_append] at hn ⊢
      rcases hn with (h | h) | h
      · exact .inl (.inl (by rw [hnames]; exact h))
      · exact .inl (.inr (hext n h))
      · exact .inr h
    exact hS.alias a (hsub a ha) b (hsub b hb) x hxa hxb (hfunc a hpa) (hfunc b hpb)

namespace ProgCtxX

variable {P : Program} {B : XEnv} {syms : String → Option Nat} (hC : ProgCtxX P B syms)
include hC

theorem indSrcX (hI : SomeInd (legalProg P)) : UnlinkIndX P B syms :=
  ⟨indScopeX_src (hC.indX hI) hC.ctx.names (fun _ h => hC.ctx.externNames h)
    (fun _ h => hC.ctx.func?_none h), (hC.ctx.ind hI).2⟩

theorem indTgtX (hI : SomeInd (legalProg P)) : UnlinkIndX (legalProg P) B syms :=
  ⟨hC.indX hI, (hC.ctx.ind hI).2⟩

end ProgCtxX

/-! ## The same code under related environments -/

/-- The extern `name` (declared with `sig`, without `i128`) of `E` returns, traps or unwinds as
`E'`'s on the same arguments. -/
def SameAtX (E E' : XEnv) (name : String) (sig : Signature) : Prop :=
  ∀ hs, E.extern name = some hs → ∃ hs', E'.extern name = some hs' ∧ ∀ vals m,
    vals.map (·.ty) = AbiParam.tys sig.params →
    (∀ rv m', hs vals m = .returned rv m' → rv.map (·.ty) = AbiParam.tys sig.returns →
      hs' vals m = .returned rv m') ∧
    (∀ c, hs vals m = .trapped c → hs' vals m = .trapped c) ∧
    (∀ e m', hs vals m = .unwound e m' → hs' vals m = .unwound e m')

/-- An indirect call with the call-site signature `d` returns, traps or raises in the target as
in the source. -/
def CallIndRelX (E E' : XEnv) (p p' : Program) (d : Signature) : Prop :=
  CallIndRel E.toEnv E'.toEnv p p' d ∧
    ∀ mem a vals r, externAtRaise E p mem d a vals = some r → externAtRaise E' p' mem d a vals = some r


theorem SameAtX.toEnv {E E' : XEnv} {name : String} {sig : Signature} (h : SameAtX E E' name sig) :
    SameAt E.toEnv E'.toEnv name sig := by
  intro hs he
  obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv he
  obtain ⟨hs', he', hrel⟩ := h gx hgx
  refine ⟨_, toEnv_extern_some he', fun vals m hv => ⟨fun rv m' ho hty => ?_, fun c ho => ?_⟩⟩
  · show (hs' vals m).toOutcome = _
    rw [(hrel vals m hv).1 rv m' (toOutcome_returned ho) hty]; rfl
  · show (hs' vals m).toOutcome = _
    rw [(hrel vals m hv).2.1 c (toOutcome_trapped ho)]; rfl

section Ident
variable {E E' : XEnv} {P P' : Program} {f : Function}
  (hext : ∀ fn e, f.extern? fn = some e → SameAtX E E' e.name e.sig)
  (hind : ∀ i d, f.sigDecls.lookup i = some d → CallIndRelX E E' P.bare P'.bare d)
  (hfree : LinkFree f)
include hext hind hfree

/-- A raise of a frame of `f` under `E` is the same raise under `E'`. -/
theorem raiseAt_ident {s : State} (hI : LFrame (P.only f) s.frame) {em : Exn × Mem}
    (h : raiseAt? E P.bare s = some em) : raiseAt? E' P'.bare s = some em := by
  have hff : s.frame.func = f := by simpa [Program.only] using hI.1
  obtain ⟨x, m1⟩ := em
  have hcall : ∀ fn args, callRaise E P.bare s.mem s.frame fn args = some (x, m1) →
      callRaise E' P'.bare s.mem s.frame fn args = some (x, m1) := by
    intro fn args h
    obtain ⟨ext, vals, g, hx, hv, ht, -, hg, hgo⟩ := callRaise_inv h
    have hx' : f.extern? fn = some ext := by rw [← hff]; exact hx
    obtain ⟨g', hg', hrel⟩ := hext fn ext hx' g hg
    exact callRaise_of hx hv ht (Program.bare_func? _ _) hg' ((hrel vals s.mem ht).2.2 x m1 hgo)
  have hind' : ∀ sig callee args, callIndRaise E P.bare s.mem s.frame sig callee args = some (x, m1) →
      callIndRaise E' P'.bare s.mem s.frame sig callee args = some (x, m1) := by
    intro sig callee args h
    obtain ⟨declared, cv, cv64, vals, hd, hc, h64, hv, -, hx⟩ := callIndRaise_inv h
    have hd' : f.sigDecls.lookup sig = some declared := by rw [← hff]; exact hd
    simp only [callIndRaise, hd, hc, h64, hv, Res.ofOption, bind, Res.bind, pure,
      Program.bare_funcs, List.find?_nil]
    exact (hind sig declared hd').2 _ _ _ _ hx
  revert h
  unfold raiseAt?
  cases hb : s.frame.body with
  | cons st rest =>
    dsimp only
    cases hi : st.inst with
    | call fn args => exact hcall fn args
    | callIndirect sig callee args => exact hind' sig callee args
    | _ => intro h; cases h
  | nil =>
    dsimp only
    cases ht : s.frame.term with
    | returnCall fn args =>
      intro _
      obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
      · rw [hff] at hB; exact absurd (hbt.symm.trans ht) (hfree B hB fn args)
      · rw [hbt] at ht; cases ht
    | tryCall fn args et =>
      dsimp only
      intro h
      rw [tryCallRaise_eq] at h ⊢
      cases hp : tryPre s.frame fn et with
      | ok q => rw [hp] at h; exact hcall fn args h
      | trap c => rw [hp] at h; cases h
      | stuck m => rw [hp] at h; cases h
    | tryCallIndirect callee args et =>
      dsimp only
      intro h
      unfold tryCallIndRaise at h ⊢
      split at h
      · exact hind' _ callee args h
      · cases h
    | _ => intro h; cases h

/-- **One step of a frame of `f` under related environments**: a step that is not stuck is the
same step. -/
theorem identX_step {s : State} (hI : LFrame (P.only f) s.frame) {r : XStepResult}
    (hr : stepX E P.bare ⟨s, []⟩ = r) (hns : ∀ msg, r ≠ .stuck msg) :
    stepX E' P'.bare ⟨s, []⟩ = r := by
  have hff : s.frame.func = f := by simpa [Program.only] using hI.1
  cases hra : raiseAt? E P.bare s with
  | some em =>
    have h' := raiseAt_ident hext hind hfree hI hra
    rw [← hr]
    simp only [stepX, hra, h']
  | none =>
    have hst : stepX E P.bare ⟨s, []⟩ = liftStep ⟨s, []⟩ (step E.toEnv P.bare s) := by
      simp only [stepX, hra]
    obtain ⟨hn, hd, ht⟩ := ident_step (E := E.toEnv) (E' := E'.toEnv) (P := P) (P' := P')
      (fun fn e he => (hext fn e he).toEnv) (fun i d hd => (hind i d hd).1) hfree hI hff
    have go : ∀ r0, step E'.toEnv P'.bare s = r0 → (∀ msg, r0 ≠ .stuck msg) →
        stepX E' P'.bare ⟨s, []⟩ = liftStep ⟨s, []⟩ r0 := by
      intro r0 h2 hn0
      have := stepX_of_not_stuck (env := E') (p := P'.bare) (xs := ⟨s, []⟩)
        (fun msg hm => hn0 msg (h2 ▸ hm))
      rw [this]
      exact congrArg _ h2
    cases hs : step E.toEnv P.bare s with
    | next s1 =>
      rw [hst, hs] at hr; rw [← hr]; exact go _ (hn s1 hs) (fun _ h => by cases h)
    | done v m =>
      rw [hst, hs] at hr; rw [← hr]; exact go _ (hd v m hs) (fun _ h => by cases h)
    | trapped c =>
      rw [hst, hs] at hr; rw [← hr]; exact go _ (ht c hs) (fun _ h => by cases h)
    | stuck msg =>
      rw [hst, hs] at hr
      exact absurd hr.symm (hns msg)

/-- **Runs of a frame of `f` under related environments**: a run that does not get stuck is the
same run. -/
theorem identX_run : ∀ (n : Nat) (s : State), s.callers = [] → LFrame (P.only f) s.frame → ∀ o,
    runLoopX E P.bare n ⟨s, []⟩ = o → (∀ msg, o ≠ .stuck msg) →
      runLoopX E' P'.bare n ⟨s, []⟩ = o := by
  intro n
  induction n with
  | zero => intro s _ _ o h _; exact h
  | succ n ih =>
    intro s hc hI o h hs
    rw [runLoopX_succ'] at h ⊢
    cases hr : stepX E P.bare ⟨s, []⟩ with
    | stuck msg => rw [hr] at h; exact absurd h.symm (hs msg)
    | next xs1 =>
      rw [hr] at h
      rw [identX_step hext hind hfree hI hr (fun _ h => by cases h)]
      obtain ⟨hcl, htr, hfr⟩ := stepX_bare_next hfree hI hc hr
      have he : xs1 = ⟨xs1.s, []⟩ := by rw [← htr]
      have h' : runLoopX E P.bare n ⟨xs1.s, []⟩ = o := by rw [← he]; exact h
      show runLoopX E' P'.bare n xs1 = o
      rw [he]
      exact ih xs1.s hcl hfr o h' hs
    | done v m =>
      rw [hr] at h; rw [identX_step hext hind hfree hI hr (fun _ h => by cases h)]; exact h
    | unwound e m =>
      rw [hr] at h; rw [identX_step hext hind hfree hI hr (fun _ h => by cases h)]; exact h
    | trapped c =>
      rw [hr] at h; rw [identX_step hext hind hfree hI hr (fun _ h => by cases h)]; exact h

end Ident

/-! ## The environments' contracts -/

section Contracts
variable {B : XEnv} {P : Program} {G : Prop} {syms : String → Option Nat} {M : Nat}

/-- The guarded environment returns memories below `2^64` (a callee's states are good). -/
theorem keep_guardX (hF : ProgFacts P) (hb : EnvKeepsBounded B.toEnv) :
    EnvKeepsBounded (guardEnvX B P G syms M).toEnv := by
  intro name g hg vals m rv m' hr hM
  obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv hg
  cases hpn : P.func? name with
  | none =>
    rw [guardEnvX_none hpn] at hgx
    exact hb name _ (toEnv_extern_some hgx) vals m rv m' hr hM
  | some h2 =>
    rw [guardEnvX_some hpn] at hgx
    cases hgx
    have hr' := toOutcome_returned hr
    obtain ⟨hh2, rfl⟩ := Program.func?_some hpn
    unfold guardFunX at hr'
    cases hi : initState P h2.name vals m with
    | ok s =>
      obtain ⟨fr', mem', he, rfl⟩ := (initState_ok_iff hpn).mp hi
      simp only [hi] at hr'
      by_cases hgd : GoodFromX B P G syms (State.toX ⟨fr', [], mem'⟩)
      · simp only [guardRX, hgd, ↓reduceIte] at hr'
        obtain ⟨u, hu, hdone⟩ := runLoopX_returned_reaches B P M _ rv m' hr'
        have hXI : XInv P (State.toX ⟨fr', [], mem'⟩) :=
          ⟨⟨LFrame.enterFunc hh2 he, fun _ h => by cases h⟩, rfl⟩
        have hLu := (hu.xinv hF.free hXI).1
        exact fun a n hv => (hgd u hu).1 a n
          (step_done_valid hF.free hLu (stepX_done_inv hdone) a n hv)
      · simp only [guardRX, hgd, ↓reduceIte] at hr'; cases hr'
    | trap c => simp only [hi] at hr'; cases hr'
    | stuck msg => simp only [hi] at hr'; cases hr'

/-- An exception a callee's run of the guarded environment raises: raised by an extern of `B`
at a good state, the memory it leaves with fewer valid ranges. -/
theorem guardX_unwound {h2 : Function} (hpn : P.func? h2.name = some h2)
    {vals : List Val} {m : Mem} {e : Exn} {m' : Mem}
    (hu : guardFunX B P G syms M h2.name vals m = .unwound e m') :
    ∃ u n g vals' mx, MemBounded u ∧ B.extern n = some g ∧ g vals' u = .unwound e mx ∧
      ∀ a k, m'.valid a k = true → mx.valid a k = true := by
  have hh2 := (Program.func?_some hpn).1
  unfold guardFunX at hu
  cases hi : initState P h2.name vals m with
  | ok s =>
    obtain ⟨fr', mem', he, rfl⟩ := (initState_ok_iff hpn).mp hi
    simp only [hi] at hu
    by_cases hgd : GoodFromX B P G syms (State.toX ⟨fr', [], mem'⟩)
    · simp only [guardRX, hgd, ↓reduceIte] at hu
      obtain ⟨u, hu', hst⟩ := runLoopX_unwound_reaches B P M _ e m' hu
      obtain ⟨n, g, vals', mx, hg, hgo, hval⟩ := stepX_unwound_extern hst
      exact ⟨u.s.mem, n, g, vals', mx, (hgd u hu').1, hg, hgo, hval⟩
    · simp only [guardRX, hgd, ↓reduceIte] at hu; cases hu
  | trap c => simp only [hi] at hu; cases hu
  | stuck msg => simp only [hi] at hu; cases hu

/-- The guarded environment unwinds with memories below `2^64`. -/
theorem keepX_guardX (hka : EnvKeepsAllocsX B) :
    EnvKeepsBoundedX (guardEnvX B P G syms M) := by
  intro name g hg vals m e m' hu hM
  cases hpn : P.func? name with
  | none =>
    rw [guardEnvX_none hpn] at hg
    exact memBounded_of_allocs (hka name g hg vals m e m' hu) hM
  | some h2 =>
    rw [guardEnvX_some hpn] at hg
    cases hg
    obtain ⟨-, rfl⟩ := Program.func?_some hpn
    obtain ⟨u, n, g', vals', mx, hub, hg', hgo, hval⟩ := guardX_unwound hpn hu
    have hmx := memBounded_of_allocs (hka n g' hg' vals' u e mx hgo) hub
    exact fun a k hv => hmx a k (hval a k hv)

/-- The guarded environment's exceptions carry two payload words. -/
theorem arity_guardX (har : ExnArityOk B) :
    ExnArityOk (guardEnvX B P G syms M) := by
  intro name g hg vals m e m' hu
  cases hpn : P.func? name with
  | none =>
    rw [guardEnvX_none hpn] at hg
    exact har name g hg vals m e m' hu
  | some h2 =>
    rw [guardEnvX_some hpn] at hg
    cases hg
    obtain ⟨-, rfl⟩ := Program.func?_some hpn
    obtain ⟨u, n, g', vals', mx, -, hg', hgo, -⟩ := guardX_unwound hpn hu
    exact har n g' hg' vals' u e mx hgo

theorem _root_.Opt.Legal.X.SReachX.reachesX {env : XEnv} {p : Program} {xs xs' : XState} (h : SReachX env p xs xs') :
    ReachesX env p xs xs' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .next hs ih

/-- The per-function run under the guarded environment from a good state traps at no load or
store (its states are whole-program states, `unlinkX_reach`). -/
theorem noMemTrapX_guard (hF : ProgFacts P) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkIndX P B syms) {s : State} (hI : UInv P f syms s)
    (hG : GoodFromX B P G syms ⟨s, []⟩) : NoMemTrapX (guardEnvX B P G syms M) P.bare s := by
  intro xs' hr
  have hW := unlinkX_reach (unlinkX_guard (G := G) (M := M) hF) hf hio hr.reachesX s rfl hI
  have hT := (hG _ hW).2.1
  intro c st rest htr hb
  have hloc : ∀ (hnc : ∀ fn args, st.inst ≠ .call fn args)
      (hnci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args),
      step (guardEnvX B P G syms M).toEnv P.bare xs'.s = step B.toEnv P xs'.s := fun hnc hnci => by
    rw [step_inst _ _ _ st rest hb hnc hnci, step_inst _ _ _ st rest hb hnc hnci]
  refine ⟨fun op ty fl a o hi => ?_, fun op ty fl x a o hi => ?_⟩
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).1 op ty fl a o hi
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).2 op ty fl x a o hi

end Contracts

/-! ## The induction -/

/-- **The refinement with unwinding at fuel `M`.** -/
def RefinesX (B : XEnv) (P : Program) (syms : String → Option Nat) (M : Nat) : Prop :=
  ∀ h ∈ P.funcs, ∀ vals vals' m fr m1 fr', enterFunc h vals m = .ok (fr, m1) →
    enterFunc (legalize h) vals' m = .ok (fr', m1) →
    ExpRel ((groups h.sig.params).getD []) vals vals' →
    GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩ →
    (∀ rv m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned rv' m2) ∧
    (∀ c, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .trapped c) ∧
    (∀ e m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2)

section Induction

variable {P : Program} {B : XEnv} {syms : String → Option Nat} (hC : ProgCtxX P B syms)
  {M : Nat} (ih : RefinesX B P syms M)
include hC ih

/-- A callee run of the guarded environment and the target's: related by the induction
hypothesis. -/
theorem prog_callX {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFunX B (legalProg P) n vals' m = .returned rv' m') ∧
    (∀ c, guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .trapped c →
      tgtFunX B (legalProg P) n vals' m = .trapped c) ∧
    (∀ e m', guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .unwound e m' →
      tgtFunX B (legalProg P) n vals' m = .unwound e m') := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.ctx.func?_some hp
  have key : ∀ o, guardFunX B P (SomeInd (legalProg P)) syms M h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩ ∧
        runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = o := by
    intro o ho hs
    unfold guardFunX at ho
    cases hi : initState P h2.name vals m with
    | ok s =>
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legal (hC.ctx.ok h2 hh2) he hexp
      simp only [hi] at ho
      by_cases hgd : GoodFromX B P (SomeInd (legalProg P)) syms (State.toX ⟨fr, [], m1⟩)
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact ⟨fr, m1, fr', he, he', hgd, ho⟩
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact absurd ho.symm (hs _)
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at ho; exact absurd ho.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = o → o ≠ .outOfFuel →
      tgtFunX B (legalProg P) h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho
    unfold tgtFunX
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    show runLimX B (legalProg P) ⟨⟨fr', [], m1⟩, []⟩ = o
    rw [runLimX_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_, fun e m' ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h)⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2.1 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2.2 e m' hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)

/-- At the declaration `n` of a function of `P` (with its signature): the environments without
unwinding are related (`ExtRelAt`), and an exception is raised alike (`ExtRaiseRel`). -/
theorem extRel_progX {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv
      (tgtEnvX B P (legalProg P)).toEnv n sig ∧
    ExtRaiseRel (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P)) n sig := by
  have hgs := guardEnvX_some (B := B) (G := SomeInd (legalProg P)) (syms := syms) (M := M) hp
  have hts := tgtEnvX_some (B := B) (P := P) (hC.ctx.func?_some hp)
  constructor
  · intro hs he
    rw [toEnv_extern_some hgs] at he
    cases he
    refine ⟨_, toEnv_extern_some hts, fun gs rg hgs' hrg vals vals' m hty hexp => ?_⟩
    have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
      rw [hsig, hgs']; exact hexp
    obtain ⟨h1, h2', -⟩ := prog_callX hC ih hp hexp'
    refine ⟨fun rv m' ho _ => ?_, fun c ho => ?_⟩
    · obtain ⟨rv', hrel, ht⟩ := h1 rv m' (toOutcome_returned ho)
      refine ⟨rv', by simp only [ht, XOutcome.toOutcome], ?_⟩
      rw [hsig, hrg] at hrel
      exact hrel
    · simp only [h2' c (toOutcome_trapped ho), XOutcome.toOutcome]
  · intro hs he
    rw [hgs] at he
    cases he
    refine ⟨_, hts, fun gs hgs' vals vals' m hty hexp e m' ho => ?_⟩
    have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
      rw [hsig, hgs']; exact hexp
    exact (prog_callX hC ih hp hexp').2.2 e m' ho

/-- At a declaration without `i128` (of a function of `P`, with its signature, or of `B`), the
two environments end alike. -/
theorem sameAtX_link {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAtX (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P)) n sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnvX_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnvX_some (hC.ctx.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2', h3⟩ := prog_callX hC ih hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho, fun e m' ho => h3 e m' ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnvX_none hpn] at he
    exact ⟨hs, by rw [tgtEnvX_none (hC.ctx.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho, fun e m' ho => ho⟩⟩

/-- An indirect call with a call-site signature without `i128`: the two environments resolve the
address to the same name and end alike. -/
theorem callIndRelX_link {d : Signature} (hd : sig128 d = false) :
    CallIndRelX (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P))
      P.bare (legalProg P).bare d := by
  have hnames : (guardEnvX B P (SomeInd (legalProg P)) syms M).names =
      (tgtEnvX B P (legalProg P)).names := rfl
  -- a function of `P` reached with a signature without `i128` has none either
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnvX B P (SomeInd (legalProg P)) syms M).sigOf n).all d.abiMatch = true →
      ((tgtEnvX B P (legalProg P)).sigOf n).all d.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys d.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : d.abiMatch h2.sig = true := by
      simpa [guardEnvX, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFacts (hC.ctx.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnvX, hC.ctx.func?_some hpn, hl2, hs']
  have hexpOf : ∀ vals n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys d.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys d.params → ExpRel ((groups h2.sig.params).getD []) vals vals := by
    intro vals n h2 _ h2p htp hv
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params h2p)
    rw [hgs, Option.getD_some]
    refine expRel_refl_plain hG (sig128_params h2p) ?_
    have := congrArg List.length (hv.trans htp)
    simpa [AbiParam.tys] using this
  have hsN : ∀ n, P.func? n = none → (tgtEnvX B P (legalProg P)).sigOf n = none := fun n hpn => by
    simp [tgtEnvX, hC.ctx.func?_none hpn]
  have hsNg : ∀ n, P.func? n = none →
      (guardEnvX B P (SomeInd (legalProg P)) syms M).sigOf n = none := fun n hpn => by
    simp [guardEnvX, hpn]
  refine ⟨fun mem a vals => ⟨fun r hr => ?_, fun c hr => ?_⟩, fun mem a vals r hr => ?_⟩
  · obtain ⟨n, g, h1, hg, hs, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hr
    have h1' : ((tgtEnvX B P (legalProg P)).toEnv.names ++ (legalProg P).bare.externNames).find?
        (fun n => mem.symbols n == some a) = some n := h1
    cases hpn : P.func? n with
    | some h2 =>
      obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv hg
      rw [guardEnvX_some hpn] at hgx
      cases hgx
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1'', -, -⟩ := prog_callX hC ih hpn (hexpOf vals n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1'' rv m' (toOutcome_returned ho)
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1', toEnv_extern_some (tgtEnvX_some
        (hC.ctx.func?_some hpn)), hs', hv, rv, m', by simp [ht, XOutcome.toOutcome], hrt, rfl⟩
    | none =>
      have hgE : (tgtEnvX B P (legalProg P)).toEnv.extern n =
          (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern n := by
        simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn), guardEnvX_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1', by rw [hgE]; exact hg,
        by simp [XEnv.toEnv, hsN n hpn], hv, rv, m', ho, hrt, rfl⟩
  · obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    have h1' : ((tgtEnvX B P (legalProg P)).toEnv.names ++ (legalProg P).bare.externNames).find?
        (fun n => mem.symbols n == some a) = some n := h1
    cases hpn : P.func? n with
    | some h2 =>
      obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv hg
      rw [guardEnvX_some hpn] at hgx
      cases hgx
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2', -⟩ := prog_callX hC ih hpn (hexpOf vals n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1', toEnv_extern_some (tgtEnvX_some
        (hC.ctx.func?_some hpn)), hs', hv, by rw [h2' c (toOutcome_trapped ho)]; rfl⟩
    | none =>
      have hgE : (tgtEnvX B P (legalProg P)).toEnv.extern n =
          (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern n := by
        simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn), guardEnvX_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1', by rw [hgE]; exact hg,
        by simp [XEnv.toEnv, hsN n hpn], hv, ho⟩
  · unfold externAtRaise at hr ⊢
    simp only [Program.bare_externNames, List.append_nil] at hr ⊢
    rw [← hnames]
    cases hf : (guardEnvX B P (SomeInd (legalProg P)) syms M).names.find?
        (fun n => mem.symbols n == some a) with
    | none => rw [hf] at hr; cases hr
    | some n =>
      rw [hf] at hr
      dsimp only at hr ⊢
      cases hpn : P.func? n with
      | some h2 =>
        rw [guardEnvX_some hpn] at hr
        rw [tgtEnvX_some (hC.ctx.func?_some hpn)]
        dsimp only at hr ⊢
        split at hr
        · rename_i hck
          simp only [Bool.and_eq_true, beq_iff_eq] at hck
          obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hck.1
          simp only [hs', hck.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          cases ho : guardFunX B P (SomeInd (legalProg P)) syms M n vals mem with
          | unwound e m' =>
            rw [ho] at hr
            rw [(prog_callX hC ih hpn (hexpOf vals n h2 hpn h2p htp hck.2)).2.2 e m' ho]
            exact hr
          | _ => rw [ho] at hr; cases hr
        · cases hr
      | none =>
        rw [guardEnvX_none hpn] at hr
        rw [tgtEnvX_none (hC.ctx.func?_none hpn), hsN n hpn]
        rw [hsNg n hpn] at hr
        exact hr

end Induction


/-! ## Entries and the refinement -/

/-- **The refinement of one activation with unwinding at fuel `M + 1`** from entry frames
(`EntryRel`), the callees related at fuel `M` (`RefinesX`). -/
theorem root_refinesX {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxX P B syms) {M : Nat} (ih : RefinesX B P syms M) {h : Function} (hh : h ∈ P.funcs)
    {args args' : List Val} {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩) :
    (∀ rv m2, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned rv' m2) ∧
    (∀ c, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .trapped c) ∧
    (∀ e m2, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2) := by
  have hF := hC.ctx.facts
  have hF' := hC.ctx.facts'
  have hhP' : legalize h ∈ (legalProg P).funcs := List.mem_map_of_mem hh
  have hio : ¬ IndFree h → SomeInd (legalProg P) := fun hn => hC.ctx.someInd hh hn
  have hLeh : LFrame (P.only h) fr := hE.lframe (by simp [Program.only])
  have hsym : ¬ IndFree h → m1.symbols = syms := fun hn => (hG _ (.refl _)).2.2 (hio hn)
  have hUI : UInv P h syms ⟨fr, [], m1⟩ := ⟨rfl, hLeh, hsym⟩
  have hioS : ¬ IndFree h → UnlinkIndX P B syms := fun hn => hC.indSrcX (hio hn)
  have hXI : XInv P ⟨⟨fr, [], m1⟩, []⟩ := ⟨⟨hE.lframe hh, fun _ h => nomatch h⟩, rfl⟩
  -- the source run is a per-function run under the guarded environment
  have hlink : ∀ o, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = o → (∀ msg, o ≠ .stuck msg) →
      o ≠ .outOfFuel → ∃ n, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = o := by
    intro o ho hs hof
    obtain ⟨n, hn⟩ := runLoopX_linkR (P := P) (env := B) (f := h) (syms := syms)
      (guardRX B P (SomeInd (legalProg P)) syms M) M ⟨⟨fr, [], m1⟩, []⟩ hF.nd hh hF.free
      (fun hn => (hioS hn).scope) (E := guardEnvX B P (SomeInd (legalProg P)) syms M) rfl rfl
      (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun t0 K T n hK hI0 hr hn _ hof' => by
        have hg := hG.callee hF.free hI0 hr
        simp only [guardRX, hg, ↓reduceIte]
        have := runLoopX_add B P n t0.toX hof' (M - n)
        rwa [Nat.add_sub_cancel' hn] at this)
      (M + 1) _ (Nat.le_refl _) (.refl _) hXI ⟨hLeh, fun _ h => nomatch h⟩ hsym
      (by rw [ho]; exact hs) (by rw [ho]; exact hof)
    exact ⟨n, hn.trans ho⟩
  -- the target's per-function run is a whole-program run
  have hUt := unlinkX_tgt (B := B) hF' hC.ctx.names (fun _ h => hC.ctx.externNames h)
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) → UnlinkIndX (legalProg P) B syms :=
    fun hn => hC.indTgtX ⟨_, hhP', hn⟩
  have hwhole : ∀ k o, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k
      ⟨⟨fr', [], m1⟩, []⟩ = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
      ∃ k', runLoopX B (legalProg P) k' ⟨⟨fr', [], m1⟩, []⟩ = o :=
    fun k o hk hs hof => unlinkX_run hUt hhP' hioT k _ hUIt o hk hs hof
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
            .returned rv' m2) ∧
      (∀ n c, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
        ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
          .trapped c) ∧
      (∀ n e m2, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
        ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
          .unwound e m2) := by
    obtain ⟨b, hb, h2, h3, h4, h5⟩ := hE.entry
    obtain ⟨b', hb', h2', h3', h5'⟩ := hE.entry'
    rcases Complete.legalOkB_cases (hC.ctx.ok h hh) with ⟨hm, -, hl⟩ | ⟨hp, cert, hc⟩
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
      have hrun := identX_run (E := guardEnvX B P (SomeInd (legalProg P)) syms M)
        (E' := tgtEnvX B P (legalProg P)) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAtX_link hC ih (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.ctx.decl h hh fn ex hfe h2 hpn))
        (fun i d hd => callIndRelX_link hC ih (by
          obtain ⟨i', hmem⟩ := lookup_mem hd
          exact hds _ hmem))
        (hC.ctx.free h hh)
      refine ⟨fun n rv m2 hr hty => ⟨rv, ?_, n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩,
        fun n c hr => ⟨n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩,
        fun n e m2 hr => ⟨n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩⟩
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      rw [hrg, Option.getD_some]
      refine expRel_refl_plain hR (sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [AbiParam.tys] using this
    · -- a legalisation: `check_refinesX2` with the two environments
      have hbase := hC.ctx.base ⟨h, hh, hp.mentions⟩
      have hbaseX := hC.baseX ⟨h, hh, hp.mentions⟩
      have hE2 : EnvOkX2 (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P))
          ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { base :=
            { src := fun _ _ _ => rfl
              tgt := fun _ _ _ => rfl
              helper := fun op => by
                obtain ⟨hf, hB, hsem⟩ := hbase.1 op
                refine ⟨hf, ?_, hsem⟩
                have : (tgtEnvX B P (legalProg P)).toEnv.extern (divHelper op) =
                    B.toEnv.extern (divHelper op) := by
                  simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none (hC.ctx.helpers op))]
                rw [this]; exact hB
              ext := fun fn ex hfe => by
                cases hpn : P.func? ex.name with
                | some h2 => exact (extRel_progX hC ih hpn (hC.ctx.decl h hh fn ex hfe h2 hpn)).1
                | none =>
                  intro hs he
                  have hgE : (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern ex.name =
                      B.toEnv.extern ex.name := by
                    simp only [XEnv.toEnv, guardEnvX_none hpn]
                  have htE : (tgtEnvX B P (legalProg P)).toEnv.extern ex.name =
                      B.toEnv.extern ex.name := by
                    simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn)]
                  rw [hgE] at he
                  obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
                  exact ⟨h', by rw [htE]; exact hb', hrel⟩
              keep := keep_guardX hF hbase.2.2
              ind := fun _ => ⟨rfl, fun B hB st hst sig callee args d hi hd =>
                (callIndRelX_link hC ih (hp.callInd B hB st hst sig callee args hi d hd)).1⟩ }
          extX := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact (extRel_progX hC ih hpn (hC.ctx.decl h hh fn ex hfe h2 hpn)).2
            | none =>
              intro hs he
              rw [guardEnvX_none hpn] at he
              exact ⟨hs, by rw [tgtEnvX_none (hC.ctx.func?_none hpn)]; exact he,
                fun gs hgs vals vals' m hty hexp e m' hu =>
                  hbaseX.1 ex.name hs he ex.sig gs hgs vals vals' m hty hexp e m' hu⟩
          keepX := keepX_guardX hbaseX.2.1
          arity := arity_guardX hbaseX.2.2
          indX := fun _ B hB st hst sig callee args d hi hd =>
            (callIndRelX_link hC ih (hp.callInd B hB st hst sig callee args hi d hd)).2 }
      have hT := noMemTrapX_guard (G := SomeInd (legalProg P)) (M := M) hF hh hioS hUI hG
      have hI : NoIndInternalX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg
      have hx := hC.exn h hh hp.mentions (legalize h) cert hc
      have href := fun n => check_refinesX2 (C := ⟨h, legalize h, cert⟩)
        (Complete.check_complete hp hc) hx hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2' h3' h5'
        hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2.1 c hr,
        fun n e m2 hr => (href n).2.2 e m2 hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_, fun e m2 hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoopX_returned_tys hF.free (M + 1) _ rv m2 hXI hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn hty
    obtain ⟨k', hk'⟩ := hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)
    exact ⟨rv', hrel, k', hk'⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    obtain ⟨k, hk⟩ := hact.2.1 n c hn
    exact hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    obtain ⟨k, hk⟩ := hact.2.2 n e m2 hn
    exact hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)

/-- **The callees are related at every fuel** (by induction on the fuel). -/
theorem prog_refinesX {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxX P B syms) : ∀ M, RefinesX B P syms M := by
  intro M
  induction M with
  | zero =>
    intro h _ vals vals' m fr m1 fr' _ _ _ _
    exact ⟨fun _ _ h => by simp [runLoopX] at h, fun _ h => by simp [runLoopX] at h,
      fun _ _ h => by simp [runLoopX] at h⟩
  | succ M ih =>
    intro h hh vals vals' m fr m1 fr' hent hent' hexp hG
    have hfacts := legalFacts (hC.ctx.ok h hh)
    exact root_refinesX hC ih hh (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG

/-- **Whole-program refinement of the original program with unwinding** (S10f): on the source
domain with unwinding (`ProgCtxX`), a whole-program run with unwinding of a function `h` of `P`
from entry frames (`EntryRel`: the target's on the ABI-split arguments, the same slots) and a
memory all of whose whole-program successors are good (`GoodFromX`) that returns within `M` steps
is a return of the legalised program's run with the results split by `h`'s return groups and the
same memory; a trap is the same trap; an exception leaving `h` is the same exception leaving
`legalize h`, with the same memory. -/
theorem legalProg_refinesX {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxX P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩) (M : Nat) :
    (∀ rv m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned rv' m2) ∧
    (∀ c, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .trapped c) ∧
    (∀ e m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2) := by
  cases M with
  | zero =>
    exact ⟨fun _ _ h => by simp [runLoopX] at h, fun _ h => by simp [runLoopX] at h,
      fun _ _ h => by simp [runLoopX] at h⟩
  | succ M => exact root_refinesX hC (prog_refinesX hC M) hh hE hG

end E2E.LegalProgram
