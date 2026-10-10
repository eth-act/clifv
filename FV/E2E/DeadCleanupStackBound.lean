import FV.E2E.StackBound
import FV.E2E.DeadCleanupLinkCheck

namespace E2E.DeadCleanupStackBound
set_option autoImplicit false
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound

abbrev Calls := E2E.StackBound.Calls
abbrev CycleFrom := @E2E.StackBound.CycleFrom

def budO (I : LinkInput) (g : Clif.Function) : Option Nat := E2E.StackBound.budC I I.resultsCleanup g

/-- The callees' stack budget of `g` (depth-independent; `0` without one). -/
def bud (I : LinkInput) (g : Clif.Function) : Nat := (budO I g).getD 0

/-- **The stack bound of `f`**: its frame plus its callees' budget. -/
def stackFn (I : LinkInput) (f : Clif.Function) : Nat := frameDrop (artOf I.resultsCleanup f).af + bud I f

/-- **The stack bound of the program**: the largest `stackFn`, when no call reaches a call cycle
(`none`: the program is recursive; `stackB_isSome_iff`). -/
def stackB (I : LinkInput) : Option Nat :=
  let R := I.resultsCleanup
  let m := budMap I R
  if (progOf R).funcs.all (fun g => (m.get? g.name).isSome) then
    some ((progOf R).funcs.foldl (fun x g => max x (frameDrop (artOf R g).af + (m.get? g.name).getD 0)) 0)
  else none

/-- The function named `n` has a budget: its calls never reach a call cycle (`goodN_iff`). -/
def goodN (I : LinkInput) (n : String) : Bool :=
  match (progOf I.resultsCleanup).func? n with
  | some f => (budO I f).isSome
  | none => false

/-- `goodN` of every name of `ns` (`budMap` evaluated once). -/
def goodAll (I : LinkInput) (ns : List String) : Bool :=
  let R := I.resultsCleanup
  let m := budMap I R
  ns.all fun n => match (progOf R).func? n with
    | some f => (m.get? f.name).isSome
    | none => false

/-! ## Soundness -/

theorem foldl_max_le {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x : Nat), x ≤ l.foldl (fun y g => max y (f g)) x
  | [], _ => Nat.le_refl _
  | g :: l, x => Nat.le_trans (Nat.le_max_left x (f g)) (foldl_max_le f l _)

theorem le_foldl_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x : Nat) {g : α}, g ∈ l → f g ≤ l.foldl (fun y g => max y (f g)) x
  | [], _, _, h => absurd h (List.not_mem_nil)
  | g' :: l, x, g, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right x (f g)) (foldl_max_le f l _)
    · exact le_foldl_max f l _ h

theorem goodN_of_all {I : LinkInput} {ns : List String} (h : goodAll I ns = true) {n : String}
    (hn : n ∈ ns) : goodN I n = true :=
  List.all_eq_true.1 h n hn

/-- `goodN` of the `k`-th name of `ns` (the generated crate proofs). -/
theorem goodN_of_idx {I : LinkInput} {ns : List String} (h : goodAll I ns = true) (k : Nat)
    (hk : k < ns.length) : goodN I ns[k] = true :=
  goodN_of_all h (List.getElem_mem hk)

/-- With the stack bound of the program, every function has a budget. -/
theorem stackB_some {I : LinkInput} {S : Nat} (hS : stackB I = some S) :
    (∀ g ∈ (progOf I.resultsCleanup).funcs, (budO I g).isSome = true) ∧
      S = (progOf I.resultsCleanup).funcs.foldl (fun x g => max x (stackFn I g)) 0 := by
  unfold stackB at hS
  dsimp only at hS
  split at hS
  · rename_i hall
    cases hS
    rw [List.all_eq_true] at hall
    exact ⟨fun g hg => hall g hg, rfl⟩
  · cases hS

/-- Every function's bound is at most the program's. -/
theorem stackFn_le {I : LinkInput} {S : Nat} (hS : stackB I = some S) {f : Clif.Function}
    (hf : f ∈ (progOf I.resultsCleanup).funcs) : stackFn I f ≤ S := by
  rw [(stackB_some hS).2]
  exact le_foldl_max _ _ _ hf

/-- Under `okB`, a callee of the linked system is an edge of the call graph. -/
theorem edgeB_of_callee {I : LinkInput} (hI : okBCleanup I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.resultsCleanup).funcs)
    (hc : (LinkSys.ofInputCleanup I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.resultsCleanup).func? n = some h := hpf
    obtain ⟨⟨e, he, hen⟩, -⟩ := siteOk_sound (site_sound (factsCleanup hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.resultsCleanup) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with hm | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okBCleanup_names hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩


theorem goodN_iff {I : LinkInput} (hI : okBCleanup I = true) {n : String} :
    goodN I n = true ↔
      ∃ f, (progOf I.resultsCleanup).func? n = some f ∧ ¬ CycleFrom (Calls I I.resultsCleanup) f := by
  unfold goodN
  cases hf : (progOf I.resultsCleanup).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okBCleanup_names hI) (Clif.Program.func?_some hf).1

/-- **The program has a stack bound iff it is not recursive**: under `okB`, `stackB I` is
`some` iff no call cycle is reachable from any function. -/
theorem stackB_isSome_iff {I : LinkInput} (hI : okBCleanup I = true) :
    (stackB I).isSome = true ↔
      ∀ f ∈ (progOf I.resultsCleanup).funcs, ¬ CycleFrom (Calls I I.resultsCleanup) f := by
  have key : (∀ f ∈ (progOf I.resultsCleanup).funcs, ¬ CycleFrom (Calls I I.resultsCleanup) f) ↔
      (progOf I.resultsCleanup).funcs.all (fun g => (E2E.StackBound.budC I I.resultsCleanup g).isSome) = true := by
    rw [List.all_eq_true]
    exact forall₂_congr fun f hf => (budC_isSome_iff (okBCleanup_names hI) hf).symm
  rw [key]
  unfold stackB E2E.StackBound.budC
  dsimp only
  split <;> simp_all

/-- The largest frame plus budget of the functions with a budget. -/
def budMax (I : LinkInput) : Nat := (progOf I.resultsCleanup).funcs.foldl (fun x g => max x (stackFn I g)) 0

/-- **Soundness of the budgets**: under `okB`, `budMap`'s budgets (which meet `budOkW`,
`budOkW_budMap`), completed by the depth budget for the functions without one
(`LinkSys.hybrid`), are a budget of the linked system of the input (whatever the base
environment). -/
theorem budget_of {I : LinkInput} (hI : okBCleanup I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (LinkSys.ofInputCleanup I B F).Budget ((LinkSys.ofInputCleanup I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (factsCleanup hI hh).depth) ?_ ?_
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.resultsCleanup) (okBCleanup_names hI)
    have he := edgeB_of_callee hI hg hcl
    have hh : h ∈ (progOf I.resultsCleanup).funcs := (LinkSys.ofInputCleanup I B F).callee_mem hcl
    simp only [E2E.StackBound.budOkW, List.all_eq_true] at hok
    have h1 := hok g hg
    change E2E.StackBound.budC I I.resultsCleanup g = some bg at hbg
    rw [hbg] at h1
    simp only [List.all_eq_true] at h1
    have h2 := h1 h hh
    simp only [edgeB] at he
    rw [he] at h2
    show ∃ bh, E2E.StackBound.budC I I.resultsCleanup h = some bh ∧ _
    cases hch : E2E.StackBound.budC I I.resultsCleanup h with
    | none => rw [hch] at h2; simp at h2
    | some bh =>
      rw [hch] at h2
      simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
      exact ⟨bh, rfl, h2⟩
  · intro h hh bh hbh
    have := le_foldl_max (stackFn I) _ 0 hh
    simp only [stackFn, bud, hbh, Option.getD_some] at this
    exact this

/-! ## The crate's theorem with the stack bound -/

/-- **`backend_correct_program_stack` for the function named `n`** of the linked system `L` of
the input `I`, every premise but `L.Ok`: for every fuel `M`, from an entry whose `sp` has
`stackFn I f` bytes below it (without wrapping) holding no code of the program, with the
addresses outside the world that stack and the code. -/
def ProgStmtS (L : LinkSys) (I : LinkInput) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s →
    stackFn I f ≤ (spv s).toNat → (∀ a, L.Img a → ¬ StackBelow (stackFn I f) (spv s) a) →
    L.F = frameWG (bud I f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

/-- **The crate's theorem with the stack bound** for its function named `n` (`CrateStmt` with
`ProgStmtS`). -/
def StackStmt (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputCleanup I B F) →
    (∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) → ProgStmtS (LinkSys.ofInputCleanup I B F) I n

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
checker refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackN {I : LinkInput} (hI : okBCleanup I = true) {n : String}
    (hn : goodN I n = true) : StackStmt I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stack _ (okBCleanup_sound hI hB hFI) (budget_of hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

/-- **Every function of an input that passes the checker and the stack check** refines at every
fuel with the stack bound `stackFn I f ≤ S` (`stackFn_le`). -/
theorem crate_correct_stack {I : LinkInput} (hI : okBCleanup I = true) {S : Nat}
    (hS : stackB I = some S) (n : String) : StackStmt I n := by
  intro B F hB hFI f hf
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  have hn : goodN I n = true := by
    unfold goodN; rw [hf']
    exact (stackB_some hS).1 f (Clif.Program.func?_some hf').1
  exact crate_correct_stackN hI hn B F hB hFI f hf

/-- **`crate_correct_stackN` from the input condition**: a function of an input that passes the
checker from which no call cycle is reachable (`goodN_iff`) refines at every fuel with its stack
bound `stackFn I f`. -/
theorem crate_correct_stack_acyclic {I : LinkInput} (hI : okBCleanup I = true) {n : String}
    {f : Clif.Function} (hf : (progOf I.resultsCleanup).func? n = some f)
    (hc : ¬ CycleFrom (Calls I I.resultsCleanup) f) : StackStmt I n :=
  crate_correct_stackN hI ((goodN_iff hI).2 ⟨f, hf, hc⟩)

/-- **`crate_correct_stack` from the input condition**: when no call cycle is reachable from any
function of an input that passes the checker, the program has a stack bound `S`
(`stackB_isSome_iff`, every function's bound at most `S`, `stackFn_le`) and every function refines
at every fuel with its bound. -/
theorem crate_correct_stack_all {I : LinkInput} (hI : okBCleanup I = true)
    (hc : ∀ f ∈ (progOf I.resultsCleanup).funcs, ¬ CycleFrom (Calls I I.resultsCleanup) f) :
    ∃ S, stackB I = some S ∧ ∀ n, StackStmt I n := by
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 ((stackB_isSome_iff hI).2 hc)
  exact ⟨S, hS, crate_correct_stack hI hS⟩

end E2E.DeadCleanupStackBound
