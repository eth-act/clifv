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
* The checker: `stackR` (the checked partial budgets), `budO`/`bud I g`, `stackFn I f` (frame
  plus budget), `stackB I` (the largest `stackFn`, when every function has a budget: `none` for
  a recursive program), `goodN I n`/`goodAll` (the function named `n` has a budget). The budgets
  are computed by iterating `B(g) = max over the callees h of g of frameDrop h + B(h)` on the
  call graph `edgeB` (an over-approximation of `LinkSys.Callee` under `okB`, `edgeB_of_callee`:
  the functions `g` declares, and with indirect calls every function with a CLIF-image address
  whose signature one of them matches; `budMap`, not trusted); `budOkW` checks that a function
  with a budget calls only functions with a budget that fit in it, and only this check enters the
  proof (`budget_of`). On a cycle no assignment passes (every compiled frame is at least 16
  bytes), so the functions that reach one have none (`budBad`) and keep
  `backend_correct_program`'s depth premise.
* `StackStmt`, `crate_correct_stackN` (`goodN I n = true`), `crate_correct_stack`
  (`stackB I = some S`, every function): the crate's theorem with the fixed bound, and
  `stackFn_le`: every function's bound is at most `S`.
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
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs) :
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

/-- One round of the budget iteration on the program's functions (by position): the callees'
largest frame plus budget, `none` while a callee has none. -/
def budStep (fd : Array Nat) (succ : Array (List Nat)) (b : Array (Option Nat)) :
    Array (Option Nat) :=
  succ.map fun hs => hs.foldl (fun acc j => match acc, b[j]! with
    | some x, some y => some (max x (fd[j]! + y))
    | _, _ => none) (some 0)

/-- At most `k` rounds, stopping at a fixed point. -/
def budIter (fd : Array Nat) (succ : Array (List Nat)) : Nat → Array (Option Nat) →
    Array (Option Nat)
  | 0, b => b
  | k + 1, b => let b' := budStep fd succ b
    if b' == b then b else budIter fd succ k b'

/-- **The computed budgets** of the functions of the results `R` whose calls never reach a call
cycle, by name (not trusted: `budOkW` checks them). After as many rounds as there are functions
exactly those have one. -/
def budMap (I : LinkInput) (R : Res) : Std.HashMap String Nat :=
  let fs := (progOf R).funcs.toArray
  let S := fun n => I.syms.lookup n
  let fd := fs.map fun g => frameDrop (artOf R g).af
  let succ := fs.map fun g =>
    let ind := !indFreeB g
    let sigs := indSigs g
    (List.range fs.size).filter fun j => edgeW S g ind sigs fs[j]!
  let b := budIter fd succ (fs.size + 1) (fs.map fun _ => none)
  (List.range fs.size).foldl (fun m j => match b[j]! with
    | some v => m.insert fs[j]!.name v
    | none => m) {}

/-- **The budget check** of partial budgets `c` of the functions of the results `R`: a function
with a budget calls (along every edge of the call graph) only functions with a budget, whose
frame and budget fit in its own. -/
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

/-- **The checked budgets** of the program with results `R` (`none` when the check fails, which
does not happen for `budMap`'s). -/
def stackR (I : LinkInput) (R : Res) : Option (Clif.Function → Option Nat) :=
  let m := budMap I R
  let c := fun g : Clif.Function => m.get? g.name
  if budOkW I R c then some c else none

/-- The functions without a budget: their calls reach a call cycle (diagnostic). -/
def budBad (I : LinkInput) (R : Res) : List String :=
  match stackR I R with
  | some c => ((progOf R).funcs.filter fun g => (c g).isNone).map (·.name)
  | none => (progOf R).funcs.map (·.name)

/-- The callees' stack budget of `g`, when its calls never reach a call cycle. -/
def budO (I : LinkInput) (g : Clif.Function) : Option Nat :=
  match stackR I I.results with
  | some c => c g
  | none => none

/-- The callees' stack budget of `g` (depth-independent; `0` without one). -/
def bud (I : LinkInput) (g : Clif.Function) : Nat := (budO I g).getD 0

/-- **The stack bound of `f`**: its frame plus its callees' budget. -/
def stackFn (I : LinkInput) (f : Clif.Function) : Nat := frameDrop (artOf I.results f).af + bud I f

/-- **The stack bound of the program**: the largest `stackFn`, when no call reaches a call cycle
(`none`: the program is recursive). -/
def stackB (I : LinkInput) : Option Nat :=
  let R := I.results
  match stackR I R with
  | some c => if (progOf R).funcs.all (fun g => (c g).isSome) then
      some ((progOf R).funcs.foldl (fun x g => max x (frameDrop (artOf R g).af + (c g).getD 0)) 0)
    else none
  | none => none

/-- The function named `n` has a budget (its calls never reach a call cycle). -/
def goodN (I : LinkInput) (n : String) : Bool :=
  match (progOf I.results).func? n with
  | some f => (budO I f).isSome
  | none => false

/-- `goodN` of every name of `ns` (`stackR` evaluated once). -/
def goodAll (I : LinkInput) (ns : List String) : Bool :=
  let R := I.results
  match stackR I R with
  | some c => ns.all fun n => match (progOf R).func? n with
    | some f => (c f).isSome
    | none => false
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

theorem stackR_ok {I : LinkInput} {R : Res} {c : Clif.Function → Option Nat}
    (h : stackR I R = some c) : budOkW I R c = true := by
  unfold stackR at h
  dsimp only at h
  split at h
  · cases h; assumption
  · cases h

theorem budO_eq {I : LinkInput} {c : Clif.Function → Option Nat}
    (h : stackR I I.results = some c) : budO I = c := by
  funext g; simp [budO, h]

theorem goodN_of_all {I : LinkInput} {ns : List String} (h : goodAll I ns = true) {n : String}
    (hn : n ∈ ns) : goodN I n = true := by
  unfold goodAll at h
  dsimp only at h
  cases hs : stackR I I.results with
  | none => rw [hs] at h; cases h
  | some c =>
    rw [hs, List.all_eq_true] at h
    have := h n hn
    unfold goodN
    rw [budO_eq hs]
    exact this

/-- With the stack bound of the program, every function has a budget. -/
theorem stackB_some {I : LinkInput} {S : Nat} (hS : stackB I = some S) :
    (∀ g ∈ (progOf I.results).funcs, (budO I g).isSome = true) ∧
      S = (progOf I.results).funcs.foldl (fun x g => max x (stackFn I g)) 0 := by
  unfold stackB at hS
  dsimp only at hS
  cases hs : stackR I I.results with
  | none => rw [hs] at hS; cases hS
  | some c =>
    rw [hs] at hS
    dsimp only at hS
    split at hS
    · rename_i hall
      cases hS
      rw [List.all_eq_true] at hall
      refine ⟨fun g hg => by rw [budO_eq hs]; exact hall g hg, ?_⟩
      simp only [stackFn, bud, budO_eq hs]
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
    rcases hmay with ⟨hm, -⟩ | ⟨hnf, -, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okB_names hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩

/-- The largest frame plus budget of the functions with a budget. -/
def budMax (I : LinkInput) : Nat := (progOf I.results).funcs.foldl (fun x g => max x (stackFn I g)) 0

/-- **Soundness of the budget check**: under `okB`, the checked budgets, completed by the depth
budget for the functions without one (`LinkSys.hybrid`), are a budget of the linked system of
the input (whatever the base environment). -/
theorem budget_of {I : LinkInput} (hI : okB I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (LinkSys.ofInput I B F).Budget ((LinkSys.ofInput I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (facts hI hh).depth) ?_ ?_
  · intro g hg bg hbg h hcl
    cases hs : stackR I I.results with
    | none => simp [budO, hs] at hbg
    | some c =>
      rw [budO_eq hs] at hbg ⊢
      have hok := stackR_ok hs
      have he := edgeB_of_callee hI hg hcl
      have hh : h ∈ (progOf I.results).funcs := (LinkSys.ofInput I B F).callee_mem hcl
      simp only [budOkW, List.all_eq_true] at hok
      have h1 := hok g hg
      rw [hbg] at h1
      simp only [List.all_eq_true] at h1
      have h2 := h1 h hh
      simp only [edgeB] at he
      rw [he] at h2
      cases hch : c h with
      | none => rw [hch] at h2; simp at h2
      | some bh => rw [hch] at h2; exact ⟨bh, rfl, by simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2; exact h2⟩
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
    TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs →
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

end StackBound

end E2E
