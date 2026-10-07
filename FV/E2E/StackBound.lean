import FV.E2E.LinkCheck

/-! # The stack bound of the functions whose calls never reach a call cycle (M9 item 4;
docs/contracts/e2e.md, "Binary level (M9)")

`backend_correct_program` (`FV/E2E/LinkArm.lean`) gives the entry activation the stack budget
`L.K M = L.D * M` for its callees, `M` the whole-program run's fuel (its step count): no fixed
stack meets it for every `M`. The linking induction holds for every per-function budget
`κ M g` in which a callee's frame and its own budget fit (`LinkSys.Budget`,
`backend_correct_program_budget`). A function whose calls never reach a cycle of the call graph
has a budget that does not depend on the depth: the largest frame chain below it. Here:

* `backend_correct_program_stack`: `backend_correct_program` with a budget that is a fixed `b` at
  the entry function, its stack premises reduced to the entry `sp` having `frameDrop f + b` bytes
  below it (without wrapping) that hold no code of the program — for **every** fuel `M`.
* `LinkSys.hybrid`, `LinkSys.budget_hybrid`: partial depth-independent budgets (for the
  functions whose calls never reach a cycle), completed by the depth budget `K M` plus a constant
  for the others, are a budget.
* The budgets: `budMap` iterates `B(g) = max over the callees h of g of frameDrop h + B(h)` on the
  call graph `edgeB` (an over-approximation of `LinkSys.Callee` under `okB`, `edgeB_of_callee`:
  the functions `g` declares, and with indirect calls every function with a CLIF-image address
  whose signature one of them matches), as many rounds as there are functions (`budArr`); by
  name `budC`/`budO`/`bud I g`, `stackFn I f` (frame plus budget), `stackB I` (the largest
  `stackFn`, when every function has a budget: `none` for a recursive program), `goodN I n`/
  `goodAll` (the function named `n` has a budget).
* Completeness (no per-program check): with distinct names (part of `okB`) the budgets meet the
  budget condition `budOkW` (a function with a budget calls only functions with a budget that
  fit in it; `budOkW_budMap`: every round of the iteration does), which is all the soundness
  proof needs (`budget_of`); and a function has a budget exactly when no call cycle of the call
  graph (`Calls`, `CycleFrom`) is reachable from it (`budC_isSome_iff`, `goodN_iff`,
  `stackB_isSome_iff`: after as many rounds as there are functions, a walk that long repeats a
  function). The functions that reach a cycle keep `backend_correct_program`'s depth premise.
* `StackStmt`, `crate_correct_stackN` (`goodN I n = true`), `crate_correct_stack`
  (`stackB I = some S`, every function): the crate's theorem with the fixed bound, and
  `stackFn_le`: every function's bound is at most `S`; `crate_correct_stack_acyclic`,
  `crate_correct_stack_all`: the same from the input condition (no call cycle reachable).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver


/-- **`backend_correct_program` with a fixed stack bound for the entry**: with a budget `κ`
(`LinkSys.Budget`) that is `b` at the entry function `f` at every depth, every run of every fuel
`M` refines, provided the entry `sp` has `frameDrop f + b` bytes below it (without wrapping)
holding no code of the program, and the addresses outside the world are that stack and the code
(`hF`). -/
theorem backend_correct_program_stack (L : LinkSys) (hL : L.Ok) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) {f : Clif.Function} (b : Nat) (hb : ∀ M, κ M f = b)
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + b ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + b) (spv s) a)
    (hF : L.F = frameWG b (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have hd := L.frameDrop_eq hL hf
  have hres : StackAvail b (L.A f).af s := by
    unfold StackAvail
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budget L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel
    hpl htr

namespace LinkSys

/-- **The budget of partial bounds** `c`: `c g = some b` (a depth-independent budget, for the
functions whose calls never reach a call cycle), else the depth budget `K M` plus a bound `C` of
the others' frames and budgets. -/
def hybrid (L : LinkSys) (c : Clif.Function → Option Nat) (C M : Nat) (g : Clif.Function) : Nat :=
  match c g with
  | some b => b
  | none => L.K M + C

/-- **`hybrid` is a budget** when the functions with a bound call only functions with a bound
that fit in theirs (`hc`) and `C` bounds every bounded function's frame and budget (`hC`). -/
theorem budget_hybrid (L : LinkSys) (c : Clif.Function → Option Nat) (C : Nat)
    (hD : ∀ h ∈ L.P.funcs, frameDrop (L.A h).af ≤ L.D)
    (hc : ∀ g ∈ L.P.funcs, ∀ bg, c g = some bg → ∀ h, L.Callee g h →
      ∃ bh, c h = some bh ∧ frameDrop (L.A h).af + bh ≤ bg)
    (hC : ∀ h ∈ L.P.funcs, ∀ bh, c h = some bh → frameDrop (L.A h).af + bh ≤ C) :
    L.Budget (L.hybrid c C) := by
  intro M g hg h hcl
  have hh := L.callee_mem hcl
  cases hg' : c g with
  | some bg =>
    obtain ⟨bh, hbh, hle⟩ := hc g hg bg hg' h hcl
    simp only [hybrid, hg', hbh]
    exact hle
  | none =>
    have hd := hD h hh
    have e : L.K (M + 1) = L.K M + L.D := by simp [K, Nat.mul_succ]
    cases hh' : c h with
    | some bh =>
      have := hC h hh bh hh'
      simp only [hybrid, hg', hh', e]
      omega
    | none =>
      simp only [hybrid, hg', hh', e]
      omega

end LinkSys

namespace StackBound

open LinkCheck

/-! ## The call graph and the budgets -/

/-- **An edge of the call graph** (an over-approximation of `LinkSys.Callee` under `okB`,
`edgeB_of_callee`, with the CLIF image's symbols `S`): `g` declares `h`, or `g` has indirect calls
(`ind`), `h` has an address and one of `g`'s indirect-call signatures (`sigs`) matches `h`'s.
`edgeB` with `ind` and `sigs` computed once per caller. -/
def edgeW (S : String → Option Nat) (g : Clif.Function) (ind : Bool) (sigs : List Clif.Signature)
    (h : Clif.Function) : Bool :=
  g.externs.any (fun e => e.2.name == h.name) ||
    (ind && (S h.name).isSome && sigs.any fun s => decide (LinkSys.IndSigMatch s h))

/-- `edgeW` of `g`'s indirect calls. -/
def edgeB (S : String → Option Nat) (g h : Clif.Function) : Bool :=
  edgeW S g (!indFreeB g) (indSigs g) h

/-- One callee `j` in a round of the budget iteration: the largest frame plus budget so far,
`none` once a callee has none. -/
def budAcc (fd : Array Nat) (b : Array (Option Nat)) (acc : Option Nat) (j : Nat) : Option Nat :=
  match acc, b[j]! with
  | some x, some y => some (max x (fd[j]! + y))
  | _, _ => none

/-- One round of the budget iteration on the program's functions (by position): the callees'
largest frame plus budget, `none` while a callee has none. -/
def budStep (fd : Array Nat) (succ : Array (List Nat)) (b : Array (Option Nat)) :
    Array (Option Nat) :=
  succ.map fun hs => hs.foldl (budAcc fd b) (some 0)

/-- At most `k` rounds, stopping at a fixed point. -/
def budIter (fd : Array Nat) (succ : Array (List Nat)) : Nat → Array (Option Nat) →
    Array (Option Nat)
  | 0, b => b
  | k + 1, b => let b' := budStep fd succ b
    if b' == b then b else budIter fd succ k b'

/-- The call graph by position: for each function of `fs`, the positions of the functions it
calls (`edgeW`, its indirect calls computed once). -/
def budSucc (I : LinkInput) (fs : Array Clif.Function) : Array (List Nat) :=
  let S := fun n => I.syms.lookup n
  fs.map fun g =>
    let ind := !indFreeB g
    let sigs := indSigs g
    (List.range fs.size).filter fun j => edgeW S g ind sigs fs[j]!

/-- The frame of each function of `fs` (by position). -/
def budFd (R : Res) (fs : Array Clif.Function) : Array Nat :=
  fs.map fun g => frameDrop (artOf R g).af

/-- **The computed budgets** of the functions of the results `R`, by position: as many rounds as
there are functions, after which exactly the functions whose calls never reach a call cycle have
one (`budC_isSome_iff`). -/
def budArr (I : LinkInput) (R : Res) : Array (Option Nat) :=
  let fs := (progOf R).funcs.toArray
  budIter (budFd R fs) (budSucc I fs) (fs.size + 1) (fs.map fun _ => none)

/-- `budArr` by name. -/
def budMap (I : LinkInput) (R : Res) : Std.HashMap String Nat :=
  let fs := (progOf R).funcs.toArray
  let b := budArr I R
  (List.range fs.size).foldl (fun m j => match b[j]! with
    | some v => m.insert fs[j]!.name v
    | none => m) {}

/-- **The budget condition** on partial budgets `c` of the functions of the results `R`: a
function with a budget calls (along every edge of the call graph) only functions with a budget,
whose frame and budget fit in its own. `budMap`'s budgets meet it (`budOkW_budMap`); it is what
the soundness proof uses (`budget_of`). -/
def budOkW (I : LinkInput) (R : Res) (c : Clif.Function → Option Nat) : Bool :=
  let S := fun n => I.syms.lookup n
  (progOf R).funcs.all fun g => match c g with
    | none => true
    | some bg =>
      let ind := !indFreeB g
      let sigs := indSigs g
      (progOf R).funcs.all fun h => !edgeW S g ind sigs h || match c h with
        | some bh => decide (frameDrop (artOf R h).af + bh ≤ bg)
        | none => false

/-- **The budgets** of the functions of the results `R` (`budMap`'s, by name): with distinct names
they meet `budOkW` (`budOkW_budMap`), and a function has one exactly when its calls reach no call
cycle (`budC_isSome_iff`). Not checked at run time. -/
def budC (I : LinkInput) (R : Res) (g : Clif.Function) : Option Nat := (budMap I R).get? g.name

/-- The callees' stack budget of `g`, when its calls never reach a call cycle. -/
def budO (I : LinkInput) (g : Clif.Function) : Option Nat := budC I I.results g

/-- The callees' stack budget of `g` (depth-independent; `0` without one). -/
def bud (I : LinkInput) (g : Clif.Function) : Nat := (budO I g).getD 0

/-- **The stack bound of `f`**: its frame plus its callees' budget. -/
def stackFn (I : LinkInput) (f : Clif.Function) : Nat := frameDrop (artOf I.results f).af + bud I f

/-- **The stack bound of the program**: the largest `stackFn`, when no call reaches a call cycle
(`none`: the program is recursive; `stackB_isSome_iff`). -/
def stackB (I : LinkInput) : Option Nat :=
  let R := I.results
  let m := budMap I R
  if (progOf R).funcs.all (fun g => (m.get? g.name).isSome) then
    some ((progOf R).funcs.foldl (fun x g => max x (frameDrop (artOf R g).af + (m.get? g.name).getD 0)) 0)
  else none

/-- The function named `n` has a budget: its calls never reach a call cycle (`goodN_iff`). -/
def goodN (I : LinkInput) (n : String) : Bool :=
  match (progOf I.results).func? n with
  | some f => (budO I f).isSome
  | none => false

/-- `goodN` of every name of `ns` (`budMap` evaluated once). -/
def goodAll (I : LinkInput) (ns : List String) : Bool :=
  let R := I.results
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
    (∀ g ∈ (progOf I.results).funcs, (budO I g).isSome = true) ∧
      S = (progOf I.results).funcs.foldl (fun x g => max x (stackFn I g)) 0 := by
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
    (hf : f ∈ (progOf I.results).funcs) : stackFn I f ≤ S := by
  rw [(stackB_some hS).2]
  exact le_foldl_max _ _ _ hf

/-- Under `okB`, a callee of the linked system is an edge of the call graph. -/
theorem edgeB_of_callee {I : LinkInput} (hI : okB I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (LinkSys.ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.results).func? n = some h := hpf
    obtain ⟨-, ⟨e, he, hen⟩, -⟩ := siteOk_sound (site_sound (facts hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.results) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with ⟨hm, -⟩ | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okB_names hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩


/-! ## Completeness: the computed budgets meet the condition, and exactly the functions whose calls
reach no call cycle have one -/

/-! ### Walks and cycles -/

/-- A walk of `k` edges of `E` from `x`. -/
inductive WalkN {α : Type} (E : α → α → Prop) : Nat → α → Prop
  | zero {x : α} : WalkN E 0 x
  | step {x y : α} {k : Nat} : E x y → WalkN E k y → WalkN E (k + 1) x

/-- **A call cycle is reachable from `x`**: a node `h` that `x` reaches in zero or more steps of
`E` (`h = x` or `TransGen E x h`) and that reaches itself in one or more. -/
def CycleFrom {α : Type} (E : α → α → Prop) (x : α) : Prop :=
  ∃ h, (h = x ∨ Relation.TransGen E x h) ∧ Relation.TransGen E h h

theorem WalkN.inv {α : Type} {E : α → α → Prop} {k : Nat} {x : α} (w : WalkN E (k + 1) x) :
    ∃ y, E x y ∧ WalkN E k y := by
  cases w with
  | step e w => exact ⟨_, e, w⟩

theorem WalkN.trunc {α : Type} {E : α → α → Prop} {k : Nat} {x : α} (w : WalkN E k x) :
    ∀ {m}, m ≤ k → WalkN E m x := by
  induction w with
  | zero => intro m hm; rw [Nat.le_zero.1 hm]; exact .zero
  | step e _ ih =>
    intro m hm
    cases m with
    | zero => exact .zero
    | succ m => exact .step e (ih (by omega))

theorem walkN_of_trans {α : Type} {E : α → α → Prop} {x y : α} (h : Relation.TransGen E x y) :
    ∀ {k}, WalkN E k y → WalkN E (k + 1) x := by
  induction h with
  | single e => exact fun w => .step e w
  | tail _ e ih => exact fun w => (ih (.step e w)).trunc (by omega)

/-- From a node that reaches a cycle start walks of every length. -/
theorem walkN_of_cycle {α : Type} {E : α → α → Prop} {x : α} (hc : CycleFrom E x) :
    ∀ k, WalkN E k x := by
  obtain ⟨h, hx, hh⟩ := hc
  have hw : ∀ k, WalkN E k h := fun k => by
    induction k with
    | zero => exact .zero
    | succ k ih => exact walkN_of_trans hh ih
  intro k
  rcases hx with rfl | hx
  · exact hw k
  · cases k with
    | zero => exact .zero
    | succ k => exact walkN_of_trans hx (hw k)

/-- The pigeonhole principle: `n + 1` values below `n` repeat. -/
theorem pigeon : ∀ (n : Nat) (f : Nat → Nat), (∀ a ≤ n, f a < n) →
    ∃ a b, a < b ∧ b ≤ n ∧ f a = f b
  | 0, _, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | n + 1, f, h => by
    by_cases hd : ∃ a, a ≤ n ∧ f a = f (n + 1)
    · obtain ⟨a, ha, he⟩ := hd
      exact ⟨a, n + 1, by omega, Nat.le_refl _, he⟩
    · have hd' : ∀ a, a ≤ n → f a ≠ f (n + 1) := fun a ha he => hd ⟨a, ha, he⟩
      have hn := h (n + 1) (Nat.le_refl _)
      obtain ⟨a, b, hab, hb, he⟩ := pigeon n (fun a => if f a = n then f (n + 1) else f a)
        fun a ha => by
          have h1 := h a (by omega)
          have h3 := hd' a ha
          split <;> omega
      refine ⟨a, b, hab, by omega, ?_⟩
      have h3 := hd' a (by omega)
      have h4 := hd' b hb
      split at he <;> split at he <;> omega

theorem WalkN.path {α : Type} {E : α → α → Prop} {k : Nat} {x : α} (w : WalkN E k x) :
    ∃ p : Nat → α, p 0 = x ∧ ∀ a < k, E (p a) (p (a + 1)) := by
  induction w with
  | @zero x => exact ⟨fun _ => x, rfl, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
  | @step x y k e _ ih =>
    obtain ⟨p, hp0, hp⟩ := ih
    refine ⟨fun a => if a = 0 then x else p (a - 1), by simp, fun a ha => ?_⟩
    cases a with
    | zero => simpa [hp0] using e
    | succ a => simpa using hp a (by omega)

theorem trans_of_path {α : Type} {E : α → α → Prop} {p : Nat → α} {k : Nat}
    (hp : ∀ a < k, E (p a) (p (a + 1))) :
    ∀ d a, a + d < k → Relation.TransGen E (p a) (p (a + d + 1))
  | 0, a, h => .single (hp a (by omega))
  | d + 1, a, h => by
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by omega]
    exact .tail (trans_of_path hp d a (by omega)) (hp (a + d + 1) (by omega))

/-- **A walk longer than the nodes reaches a cycle**: on a graph whose edges end in `dom`, a walk
of `dom.length` edges from a node of `dom` reaches a cycle. -/
theorem cycle_of_walkN {α : Type} {E : α → α → Prop} (dom : List α)
    (hdom : ∀ x y, E x y → y ∈ dom) {x : α} (hx : x ∈ dom) (w : WalkN E dom.length x) :
    CycleFrom E x := by
  classical
  obtain ⟨p, hp0, hp⟩ := w.path
  have hmem : ∀ a ≤ dom.length, p a ∈ dom := by
    intro a ha
    cases a with
    | zero => rw [hp0]; exact hx
    | succ a => exact hdom _ _ (hp a (by omega))
  obtain ⟨a, b, hab, hb, he⟩ := pigeon dom.length (fun a => dom.idxOf (p a))
    fun a ha => List.idxOf_lt_length_of_mem (hmem a ha)
  have heq : p a = p b := by
    have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem a (by omega)))
    have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem b hb))
    simp only [he] at h1
    exact h1.symm.trans h2
  refine ⟨p a, ?_, ?_⟩
  · cases a with
    | zero => exact .inl hp0
    | succ a =>
      have := trans_of_path hp a 0 (by omega)
      rw [hp0, show 0 + a + 1 = a + 1 by omega] at this
      exact .inr this
  · have := trans_of_path hp (b - a - 1) a (by omega)
    rw [show a + (b - a - 1) + 1 = b by omega, ← heq] at this
    exact this

/-! ### The iteration -/

/-- `budStep` iterated `k` times from `b₀`. -/
def budPow (fd : Array Nat) (succ : Array (List Nat)) (b₀ : Array (Option Nat)) :
    Nat → Array (Option Nat)
  | 0 => b₀
  | k + 1 => budStep fd succ (budPow fd succ b₀ k)

/-- The call graph by position. -/
def IdxE (succ : Array (List Nat)) (i j : Nat) : Prop := j ∈ succ[i]!

section
variable {fd : Array Nat} {succ : Array (List Nat)} {b₀ : Array (Option Nat)}

theorem budAcc_none (b : Array (Option Nat)) :
    ∀ hs : List Nat, hs.foldl (budAcc fd b) none = none
  | [] => rfl
  | _ :: hs => budAcc_none b hs

theorem budAcc_some (b : Array (Option Nat)) :
    ∀ (hs : List Nat) (a v : Nat), hs.foldl (budAcc fd b) (some a) = some v →
      a ≤ v ∧ ∀ j ∈ hs, ∃ y, b[j]! = some y ∧ fd[j]! + y ≤ v
  | [], a, v, h => by cases h; exact ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | j :: hs, a, v, h => by
    rw [List.foldl_cons] at h
    cases hb : b[j]! with
    | none =>
      rw [show budAcc fd b (some a) j = none by simp [budAcc, hb], budAcc_none] at h
      cases h
    | some y =>
      rw [show budAcc fd b (some a) j = some (max a (fd[j]! + y)) by simp [budAcc, hb]] at h
      obtain ⟨h1, h2⟩ := budAcc_some b hs _ v h
      refine ⟨by omega, fun j' hj' => ?_⟩
      rcases List.mem_cons.1 hj' with rfl | hj'
      · exact ⟨y, hb, by omega⟩
      · exact h2 j' hj'

theorem budAcc_isSome (b : Array (Option Nat)) :
    ∀ (hs : List Nat) (a : Nat), (∀ j ∈ hs, (b[j]!).isSome = true) →
      (hs.foldl (budAcc fd b) (some a)).isSome = true
  | [], _, _ => rfl
  | j :: hs, a, h => by
    rw [List.foldl_cons]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h j List.mem_cons_self)
    rw [show budAcc fd b (some a) j = some (max a (fd[j]! + y)) by simp [budAcc, hy]]
    exact budAcc_isSome b hs _ fun j' hj' => h j' (List.mem_cons_of_mem _ hj')

theorem budAcc_congr {b b' : Array (Option Nat)} :
    ∀ (hs : List Nat) (acc : Option Nat), (∀ j ∈ hs, b[j]! = b'[j]!) →
      hs.foldl (budAcc fd b) acc = hs.foldl (budAcc fd b') acc
  | [], _, _ => rfl
  | j :: hs, acc, h => by
    rw [List.foldl_cons, List.foldl_cons,
      show budAcc fd b acc j = budAcc fd b' acc j by simp only [budAcc, h j List.mem_cons_self]]
    exact budAcc_congr hs _ fun j' hj' => h j' (List.mem_cons_of_mem _ hj')

theorem budStep_get (b : Array (Option Nat)) (i : Nat) :
    (budStep fd succ b)[i]! =
      if i < succ.size then succ[i]!.foldl (budAcc fd b) (some 0) else none := by
  split
  · rename_i h
    rw [getElem!_pos _ _ (by simp [budStep, h]), getElem!_pos succ i h]
    simp [budStep]
  · rename_i h
    rw [getElem!_neg _ _ (by simp [budStep, h])]
    rfl

theorem budStep_some {b : Array (Option Nat)} {i v : Nat} (h : (budStep fd succ b)[i]! = some v) :
    i < succ.size ∧ succ[i]!.foldl (budAcc fd b) (some 0) = some v := by
  rw [budStep_get] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-- A budget, once computed, stays. -/
theorem budPow_mono (hb₀ : ∀ j : Nat, b₀[j]! = none) :
    ∀ (k j v : Nat), (budPow fd succ b₀ k)[j]! = some v → (budPow fd succ b₀ (k + 1))[j]! = some v
  | 0, j, v, h => by simp [budPow, hb₀] at h
  | k + 1, j, v, h => by
    obtain ⟨hj, hf⟩ := budStep_some h
    obtain ⟨-, hall⟩ := budAcc_some _ _ _ _ hf
    show (budStep fd succ (budPow fd succ b₀ (k + 1)))[j]! = some v
    simp only [budStep_get, hj, ↓reduceIte]
    rw [← hf]
    refine (budAcc_congr _ _ fun j' hj' => ?_).symm
    obtain ⟨y, hy, -⟩ := hall j' hj'
    rw [hy, budPow_mono hb₀ k j' y hy]

/-- **Every iterate passes the budget check**: a position with a budget has its callees' budgets,
whose frame and budget fit. -/
theorem budPow_ok (hb₀ : ∀ j : Nat, b₀[j]! = none) :
    ∀ (k i bg : Nat), (budPow fd succ b₀ k)[i]! = some bg → ∀ j ∈ succ[i]!,
      ∃ bh, (budPow fd succ b₀ k)[j]! = some bh ∧ fd[j]! + bh ≤ bg
  | 0, i, bg, h => by simp [budPow, hb₀] at h
  | k + 1, i, bg, h => by
    obtain ⟨-, hf⟩ := budStep_some h
    intro j hj
    obtain ⟨bh, hbh, hle⟩ := (budAcc_some _ _ _ _ hf).2 j hj
    exact ⟨bh, budPow_mono hb₀ k j bh hbh, hle⟩

/-- A position with a budget after `k` rounds has no walk of `k` calls. -/
theorem budPow_walk (hb₀ : ∀ j : Nat, b₀[j]! = none) :
    ∀ (k i v : Nat), (budPow fd succ b₀ k)[i]! = some v → ¬ WalkN (IdxE succ) k i
  | 0, i, v, h => by simp [budPow, hb₀] at h
  | k + 1, i, v, h => fun w => by
    obtain ⟨-, hf⟩ := budStep_some h
    obtain ⟨j, hj, w'⟩ := w.inv
    obtain ⟨y, hy, -⟩ := (budAcc_some _ _ _ _ hf).2 j hj
    exact budPow_walk hb₀ k j y hy w'

/-- A position without a walk of `k` calls has a budget after `k` rounds. -/
theorem budPow_of_walk (hsucc : ∀ i j : Nat, j ∈ succ[i]! → j < succ.size) :
    ∀ (k i : Nat), i < succ.size → ¬ WalkN (IdxE succ) k i → (budPow fd succ b₀ k)[i]!.isSome = true
  | 0, _, _, h => absurd .zero h
  | k + 1, i, hi, h => by
    show (budStep fd succ (budPow fd succ b₀ k))[i]!.isSome = true
    simp only [budStep_get, hi, ↓reduceIte]
    exact budAcc_isSome _ _ _ fun j hj =>
      budPow_of_walk hsucc k j (hsucc i j hj) fun w => h (.step hj w)

theorem budPow_fix {m : Nat} (h : budStep fd succ (budPow fd succ b₀ m) = budPow fd succ b₀ m) :
    ∀ t, budPow fd succ b₀ (m + t) = budPow fd succ b₀ m
  | 0 => rfl
  | t + 1 => by
    show budStep fd succ (budPow fd succ b₀ (m + t)) = _
    rw [budPow_fix h t, h]

/-- `budIter` returns an iterate: after all its rounds, or at a fixed point. -/
theorem budIter_pow : ∀ k j, ∃ m, budIter fd succ k (budPow fd succ b₀ j) = budPow fd succ b₀ m ∧
    (m = j + k ∨ budStep fd succ (budPow fd succ b₀ m) = budPow fd succ b₀ m)
  | 0, j => ⟨j, rfl, .inl rfl⟩
  | k + 1, j => by
    simp only [budIter]
    split
    · exact ⟨j, rfl, .inr (eq_of_beq (by assumption))⟩
    · obtain ⟨m, hm, h⟩ := budIter_pow k (j + 1)
      exact ⟨m, hm, h.imp_left fun h => by omega⟩

/-- `budIter` with fuel `n + 1` from `b₀` returns an iterate of at least `n` rounds. -/
theorem budIter_ge (n : Nat) : ∃ m, n ≤ m ∧ budIter fd succ (n + 1) b₀ = budPow fd succ b₀ m := by
  obtain ⟨m, hm, h⟩ := budIter_pow (fd := fd) (succ := succ) (b₀ := b₀) (n + 1) 0
  rcases h with h | h
  · exact ⟨m, by omega, hm⟩
  · exact ⟨m + (n + 1), by omega, by rw [budPow_fix h]; exact hm⟩

end


/-! ### The program's call graph and the computed budgets -/

/-- **The call graph** of the program of the results `R`: `h` is one of its functions and `g` may
call it (`edgeB`; under `okB` every callee of the linked system is one, `edgeB_of_callee`). -/
def Calls (I : LinkInput) (R : Res) (g h : Clif.Function) : Prop :=
  h ∈ (progOf R).funcs ∧ edgeB (fun n => I.syms.lookup n) g h = true

theorem mem_toArray {l : List Clif.Function} {g : Clif.Function} (hg : g ∈ l) :
    ∃ i, i < l.toArray.size ∧ l.toArray[i]! = g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  exact ⟨i, by simpa using hi, by simp [hi]⟩

theorem toArray_mem {l : List Clif.Function} {i : Nat} (hi : i < l.toArray.size) :
    l.toArray[i]! ∈ l := by
  simp only [List.size_toArray] at hi
  simp [hi]

theorem budSucc_size (I : LinkInput) (fs : Array Clif.Function) : (budSucc I fs).size = fs.size := by
  simp [budSucc]

theorem budSucc_mem {I : LinkInput} {fs : Array Clif.Function} {i j : Nat} (hi : i < fs.size) :
    j ∈ (budSucc I fs)[i]! ↔ j < fs.size ∧ edgeB (fun n => I.syms.lookup n) fs[i]! fs[j]! = true := by
  rw [getElem!_pos _ _ (by simp [budSucc, hi]), getElem!_pos fs i hi]
  simp [budSucc, edgeB, List.mem_filter, List.mem_range]

theorem budSucc_lt (I : LinkInput) (fs : Array Clif.Function) :
    ∀ i j : Nat, j ∈ (budSucc I fs)[i]! → j < (budSucc I fs).size := by
  intro i j h
  rw [budSucc_size]
  by_cases hi : i < fs.size
  · exact ((budSucc_mem hi).1 h).1
  · rw [getElem!_neg _ _ (by simp [budSucc, hi])] at h
    exact absurd h List.not_mem_nil

theorem budFd_get (R : Res) {fs : Array Clif.Function} {j : Nat} (hj : j < fs.size) :
    (budFd R fs)[j]! = frameDrop (artOf R fs[j]!).af := by
  rw [getElem!_pos _ _ (by simp [budFd, hj]), getElem!_pos fs j hj]
  simp [budFd]

theorem budNone (fs : Array Clif.Function) (j : Nat) :
    (fs.map fun _ => (none : Option Nat))[j]! = none := by
  by_cases hj : j < fs.size
  · rw [getElem!_pos _ _ (by simp [hj])]
    simp
  · rw [getElem!_neg _ _ (by simp [hj])]
    rfl

/-- `budArr` is an iterate of at least as many rounds as there are functions. -/
theorem budArr_pow (I : LinkInput) (R : Res) :
    ∃ m, (progOf R).funcs.toArray.size ≤ m ∧ budArr I R = budPow (budFd R (progOf R).funcs.toArray)
      (budSucc I (progOf R).funcs.toArray) ((progOf R).funcs.toArray.map fun _ => none) m :=
  budIter_ge _

/-- The by-name map of the budgets by position, with distinct names. -/
theorem foldIns_get (fs : Array Clif.Function) (b : Array (Option Nat)) {i : Nat}
    (hinj : ∀ j, j < fs.size → fs[j]!.name = fs[i]!.name → j = i) :
    ∀ (l : List Nat) (m : Std.HashMap String Nat), (∀ j ∈ l, j < fs.size) →
      (l.foldl (fun m j => match b[j]! with
        | some v => m.insert fs[j]!.name v
        | none => m) m).get? fs[i]!.name =
        if i ∈ l then (b[i]!).or (m.get? fs[i]!.name) else m.get? fs[i]!.name
  | [], m, _ => by simp
  | j :: l, m, hl => by
    rw [List.foldl_cons, foldIns_get fs b hinj l _ fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')]
    have hstep : (match b[j]! with
        | some v => m.insert fs[j]!.name v
        | none => m).get? fs[i]!.name =
        if j = i then (b[i]!).or (m.get? fs[i]!.name) else m.get? fs[i]!.name := by
      by_cases hji : j = i
      · subst hji
        cases b[j]! <;> simp
      · have hne : fs[j]!.name ≠ fs[i]!.name := fun h => hji (hinj j (hl j List.mem_cons_self) h)
        cases b[j]! <;> simp [Std.HashMap.getElem?_insert, hne, hji]
    rw [hstep]
    by_cases hil : i ∈ l
    · simp only [hil, List.mem_cons, or_true, ite_true]
      split <;> cases b[i]! <;> rfl
    · by_cases hji : j = i
      · subst hji; simp [hil]
      · have hij : ¬ i = j := fun h => hji h.symm
        simp [hil, hji, hij]

/-- With distinct names, a function's budget is its position's. -/
theorem budC_get {I : LinkInput} {R : Res} (hn : ((progOf R).funcs.map (·.name)).Nodup) {i : Nat}
    (hi : i < (progOf R).funcs.toArray.size) :
    budC I R (progOf R).funcs.toArray[i]! = (budArr I R)[i]! := by
  have hinj : ∀ j, j < (progOf R).funcs.toArray.size →
      (progOf R).funcs.toArray[j]!.name = (progOf R).funcs.toArray[i]!.name → j = i := by
    intro j hj h
    simp only [List.size_toArray] at hi hj
    simp only [getElem!_pos (progOf R).funcs.toArray j (by simpa using hj),
      getElem!_pos (progOf R).funcs.toArray i (by simpa using hi), List.getElem_toArray] at h
    exact hn.eq_of_getElem_eq (by simpa using hj) (by simpa using hi) (by simpa using h)
  unfold budC budMap
  dsimp only
  rw [foldIns_get _ _ hinj _ _ fun j hj => by simpa using hj]
  simp [List.mem_range.2 (by simpa using hi)]

/-- **Completeness of the budget condition**: with distinct names (part of `okB`, `okB_names`),
`budMap`'s budgets meet `budOkW`. -/
theorem budOkW_budMap {I : LinkInput} {R : Res} (hn : ((progOf R).funcs.map (·.name)).Nodup) :
    budOkW I R (budC I R) = true := by
  obtain ⟨m, -, hm⟩ := budArr_pow I R
  simp only [budOkW, List.all_eq_true]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := mem_toArray hg
  rw [budC_get hn hi, hm]
  cases hb : (budPow _ _ _ m)[i]! with
  | none => rfl
  | some bg =>
    simp only [List.all_eq_true]
    intro h hh
    obtain ⟨j, hj, rfl⟩ := mem_toArray hh
    cases he : edgeW (fun n => I.syms.lookup n) (progOf R).funcs.toArray[i]!
      (!indFreeB (progOf R).funcs.toArray[i]!) (indSigs (progOf R).funcs.toArray[i]!)
      (progOf R).funcs.toArray[j]!
    · rfl
    · obtain ⟨bh, hbh, hle⟩ := budPow_ok (budNone _) m i bg hb j ((budSucc_mem hi).2 ⟨hj, he⟩)
      rw [budC_get hn hj, hm, hbh]
      rw [budFd_get R hj] at hle
      simpa using hle

theorem walk_idx {I : LinkInput} {R : Res} :
    ∀ {k i : Nat}, i < (progOf R).funcs.toArray.size →
      (WalkN (IdxE (budSucc I (progOf R).funcs.toArray)) k i ↔
        WalkN (Calls I R) k (progOf R).funcs.toArray[i]!)
  | 0, _, _ => ⟨fun _ => .zero, fun _ => .zero⟩
  | k + 1, i, hi => by
    constructor
    · intro w
      obtain ⟨j, hj, w'⟩ := w.inv
      obtain ⟨hjN, he⟩ := (budSucc_mem hi).1 hj
      exact .step ⟨toArray_mem hjN, he⟩ ((walk_idx hjN).1 w')
    · intro w
      obtain ⟨h, ⟨hh, he⟩, w'⟩ := w.inv
      obtain ⟨j, hj, rfl⟩ := mem_toArray hh
      exact .step ((budSucc_mem hi).2 ⟨hj, he⟩) ((walk_idx hj).2 w')

/-- **Exactly the functions whose calls reach no call cycle have a budget** (with distinct
names). -/
theorem budC_isSome_iff {I : LinkInput} {R : Res} (hn : ((progOf R).funcs.map (·.name)).Nodup)
    {g : Clif.Function} (hg : g ∈ (progOf R).funcs) :
    (budC I R g).isSome = true ↔ ¬ CycleFrom (Calls I R) g := by
  obtain ⟨i, hi, rfl⟩ := mem_toArray hg
  obtain ⟨m, hm, hb⟩ := budArr_pow I R
  rw [budC_get hn hi, hb]
  constructor
  · intro hs hc
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact budPow_walk (budNone _) m i v hv ((walk_idx hi).2 (walkN_of_cycle hc m))
  · intro hc
    refine budPow_of_walk (budSucc_lt I _) m i (by rw [budSucc_size]; exact hi) fun w => hc ?_
    have w' := ((walk_idx hi).1 w).trunc hm
    exact cycle_of_walkN (progOf R).funcs (fun _ _ h => h.1) hg (by simpa using w')

/-- **`goodN` is the input condition**: under `okB`, the function named `n` has a budget iff it
is a function of the program from which no call cycle is reachable. -/
theorem goodN_iff {I : LinkInput} (hI : okB I = true) {n : String} :
    goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ CycleFrom (Calls I I.results) f := by
  unfold goodN
  cases hf : (progOf I.results).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okB_names hI) (Clif.Program.func?_some hf).1

/-- **The program has a stack bound iff it is not recursive**: under `okB`, `stackB I` is
`some` iff no call cycle is reachable from any function. -/
theorem stackB_isSome_iff {I : LinkInput} (hI : okB I = true) :
    (stackB I).isSome = true ↔
      ∀ f ∈ (progOf I.results).funcs, ¬ CycleFrom (Calls I I.results) f := by
  have key : (∀ f ∈ (progOf I.results).funcs, ¬ CycleFrom (Calls I I.results) f) ↔
      (progOf I.results).funcs.all (fun g => (budC I I.results g).isSome) = true := by
    rw [List.all_eq_true]
    exact forall₂_congr fun f hf => (budC_isSome_iff (okB_names hI) hf).symm
  rw [key]
  unfold stackB budC
  dsimp only
  split <;> simp_all

/-- The largest frame plus budget of the functions with a budget. -/
def budMax (I : LinkInput) : Nat := (progOf I.results).funcs.foldl (fun x g => max x (stackFn I g)) 0

/-- **Soundness of the budgets**: under `okB`, `budMap`'s budgets (which meet `budOkW`,
`budOkW_budMap`), completed by the depth budget for the functions without one
(`LinkSys.hybrid`), are a budget of the linked system of the input (whatever the base
environment). -/
theorem budget_of {I : LinkInput} (hI : okB I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (LinkSys.ofInput I B F).Budget ((LinkSys.ofInput I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (facts hI hh).depth) ?_ ?_
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.results) (okB_names hI)
    have he := edgeB_of_callee hI hg hcl
    have hh : h ∈ (progOf I.results).funcs := (LinkSys.ofInput I B F).callee_mem hcl
    simp only [budOkW, List.all_eq_true] at hok
    have h1 := hok g hg
    change budC I I.results g = some bg at hbg
    rw [hbg] at h1
    simp only [List.all_eq_true] at h1
    have h2 := h1 h hh
    simp only [edgeB] at he
    rw [he] at h2
    show ∃ bh, budC I I.results h = some bh ∧ _
    cases hch : budC I I.results h with
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
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInput I B F) →
    (∀ a, (LinkSys.ofInput I B F).Img a → F a) → ProgStmtS (LinkSys.ofInput I B F) I n

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
checker refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackN {I : LinkInput} (hI : okB I = true) {n : String}
    (hn : goodN I n = true) : StackStmt I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stack _ (okB_sound hI hB hFI) (budget_of hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

/-- **Every function of an input that passes the checker and the stack check** refines at every
fuel with the stack bound `stackFn I f ≤ S` (`stackFn_le`). -/
theorem crate_correct_stack {I : LinkInput} (hI : okB I = true) {S : Nat}
    (hS : stackB I = some S) (n : String) : StackStmt I n := by
  intro B F hB hFI f hf
  have hf' : (progOf I.results).func? n = some f := hf
  have hn : goodN I n = true := by
    unfold goodN; rw [hf']
    exact (stackB_some hS).1 f (Clif.Program.func?_some hf').1
  exact crate_correct_stackN hI hn B F hB hFI f hf

/-- **`crate_correct_stackN` from the input condition**: a function of an input that passes the
checker from which no call cycle is reachable (`goodN_iff`) refines at every fuel with its stack
bound `stackFn I f`. -/
theorem crate_correct_stack_acyclic {I : LinkInput} (hI : okB I = true) {n : String}
    {f : Clif.Function} (hf : (progOf I.results).func? n = some f)
    (hc : ¬ CycleFrom (Calls I I.results) f) : StackStmt I n :=
  crate_correct_stackN hI ((goodN_iff hI).2 ⟨f, hf, hc⟩)

/-- **`crate_correct_stack` from the input condition**: when no call cycle is reachable from any
function of an input that passes the checker, the program has a stack bound `S`
(`stackB_isSome_iff`, every function's bound at most `S`, `stackFn_le`) and every function refines
at every fuel with its bound. -/
theorem crate_correct_stack_all {I : LinkInput} (hI : okB I = true)
    (hc : ∀ f ∈ (progOf I.results).funcs, ¬ CycleFrom (Calls I I.results) f) :
    ∃ S, stackB I = some S ∧ ∀ n, StackStmt I n := by
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 ((stackB_isSome_iff hI).2 hc)
  exact ⟨S, hS, crate_correct_stack hI hS⟩

end StackBound

end E2E
