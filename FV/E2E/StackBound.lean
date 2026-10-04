import FV.E2E.LinkCheck

/-! # The stack bound of a program without recursion (M9 item 4; docs/contracts/e2e.md,
"Binary level (M9)")

`backend_correct_program` (`FV/E2E/LinkArm.lean`) gives the entry activation the stack budget
`L.K M = L.D * M` for its callees, `M` the whole-program run's fuel (its step count): no fixed
stack meets it for every `M`. The linking induction holds for every per-function budget
`κ M g` in which a callee's frame and its own budget fit (`LinkSys.Budget`,
`backend_correct_program_budget`). For a program whose call graph has no cycle, a budget that does
not depend on the depth exists: the largest frame chain below each function. Here:

* `backend_correct_program_stack`: `backend_correct_program` with a depth-independent budget
  `B : Clif.Function → Nat` (`L.Budget fun _ g => B g`), its stack premises reduced to the entry
  `sp` having `frameDrop f + B f` bytes below it (without wrapping) that hold no code of the
  program — for **every** fuel `M`.
* `stackR`, `bud I`, `stackFn I f`, `stackB I`: the checker. The budgets are computed by
  iterating `B(g) = max over the callees h of g of frameDrop h + B(h)` on the call graph `edgeB`
  (an over-approximation of `LinkSys.Callee` under `okB`, `edgeB_of_callee`: the functions `g`
  declares, and with indirect calls every function with a CLIF-image address whose signature one
  of them matches; `budMap`, not trusted); `budOkW` checks the inequality on every edge, and only
  this check enters the proof (`budget_of`). On a cycle no assignment passes (every compiled frame
  is at least 16 bytes), so `stackB I` is `none` for recursive programs (`budBad`: the functions
  where the check fails), which keep `backend_correct_program`'s depth premise.
* `StackStmt`, `crate_correct_stack`: the crate's theorem with the fixed bound
  (`okB I = true → stackB I = some S → StackStmt I n`), and `stackFn_le`: every function's bound
  is at most `S`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_program` with a depth-independent stack bound**: with a budget `B` in which
every program callee's frame and budget fit (`L.Budget fun _ g => B g`), every run of every fuel
`M` refines, provided the entry `sp` has `frameDrop f + B f` bytes below it (without wrapping)
holding no code of the program, and the addresses outside the world are that stack and the code
(`hF`). -/
theorem backend_correct_program_stack (L : LinkSys) (hL : L.Ok) (B : Clif.Function → Nat)
    (hB : L.Budget fun _ g => B g) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + B f ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + B f) (spv s) a)
    (hF : L.F = frameWG (B f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
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
  have hres : StackAvail (B f) (L.A f).af s := by
    unfold StackAvail
    rw [show (L.A f).af.frameSize + 16 + B f = frameDrop (L.A f).af + B f by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  exact backend_correct_program_budget L hL (κ := fun _ g => B g) hB hf M hent hres hF hgfree himg
    hbe hargs hcs hsav hrel hpl htr

namespace StackBound

open LinkCheck

/-! ## The call graph and the budget -/

/-- **An edge of the call graph** (an over-approximation of `LinkSys.Callee` under `okB`, with
the CLIF image's symbols `S`): `g` declares `h`, or `g` has indirect calls (`ind`), `h` has an
address and one of `g`'s indirect-call signatures (`sigs`) matches `h`'s. `edgeB` with `ind` and
`sigs` computed once per caller. -/
def edgeW (S : String → Option Nat) (g : Clif.Function) (ind : Bool) (sigs : List Clif.Signature)
    (h : Clif.Function) : Bool :=
  g.externs.any (fun e => e.2.name == h.name) ||
    (ind && (S h.name).isSome && sigs.any fun s => decide (LinkSys.IndSigMatch s h))

/-- `edgeW` of `g`'s indirect calls. -/
def edgeB (S : String → Option Nat) (g h : Clif.Function) : Bool :=
  edgeW S g (!indFreeB g) (indSigs g) h

/-- One round of the budget iteration on the program's functions (by position): the callees'
largest frame plus budget. -/
def budStep (fd : Array Nat) (succ : Array (List Nat)) (b : Array Nat) : Array Nat :=
  succ.map fun hs => hs.foldl (fun x j => max x (fd[j]! + b[j]!)) 0

/-- At most `k` rounds, stopping at a fixed point. -/
def budIter (fd : Array Nat) (succ : Array (List Nat)) : Nat → Array Nat → Array Nat
  | 0, b => b
  | k + 1, b => let b' := budStep fd succ b
    if b' == b then b else budIter fd succ k b'

/-- **The computed budgets** of the functions of the results `R`, by name (not trusted:
`budOkW` checks them). On a call graph without cycles the iteration reaches its fixed point
within as many rounds as there are functions. -/
def budMap (I : LinkInput) (R : Res) : Std.HashMap String Nat :=
  let fs := (progOf R).funcs.toArray
  let S := fun n => I.syms.lookup n
  let fd := fs.map fun g => frameDrop (artOf R g).af
  let succ := fs.map fun g =>
    let ind := !indFreeB g
    let sigs := indSigs g
    (List.range fs.size).filter fun j => edgeW S g ind sigs fs[j]!
  let b := budIter fd succ (fs.size + 1) (fs.map fun _ => 0)
  (List.range fs.size).foldl (fun m j => m.insert fs[j]!.name b[j]!) {}

/-- **The budget check** of a budget `b` of the functions of the results `R`: on every edge of
the call graph the callee's frame and budget fit in the caller's budget. -/
def budOkW (I : LinkInput) (R : Res) (b : Clif.Function → Nat) : Bool :=
  let S := fun n => I.syms.lookup n
  (progOf R).funcs.all fun g =>
    let ind := !indFreeB g
    let sigs := indSigs g
    (progOf R).funcs.all fun h =>
      !edgeW S g ind sigs h || decide (frameDrop (artOf R h).af + b h ≤ b g)

/-- The functions on which the budget check fails (diagnostic: they reach a call cycle). -/
def budBad (I : LinkInput) (R : Res) (b : Clif.Function → Nat) : List String :=
  let S := fun n => I.syms.lookup n
  ((progOf R).funcs.filter fun g =>
    let ind := !indFreeB g
    let sigs := indSigs g
    !(progOf R).funcs.all fun h =>
      !edgeW S g ind sigs h || decide (frameDrop (artOf R h).af + b h ≤ b g)).map (·.name)

/-- **The stack bound of the program with results `R`**: `(budget, bound)` — the depth-independent
callees' budget of every function, and the largest frame plus budget — when the budget check
passes (`none`: the call graph has a cycle). -/
def stackR (I : LinkInput) (R : Res) : Option ((Clif.Function → Nat) × Nat) :=
  let m := budMap I R
  let b := fun g : Clif.Function => m.getD g.name 0
  if budOkW I R b then
    some (b, (progOf R).funcs.foldl (fun x g => max x (frameDrop (artOf R g).af + b g)) 0)
  else none

/-- The callees' stack budget of `g` (depth-independent; `0` when the check fails). -/
def bud (I : LinkInput) (g : Clif.Function) : Nat :=
  match stackR I I.results with
  | some (b, _) => b g
  | none => 0

/-- **The stack bound of `f`**: its frame plus its callees' budget. -/
def stackFn (I : LinkInput) (f : Clif.Function) : Nat := frameDrop (artOf I.results f).af + bud I f

/-- **The stack bound of the program** (`none`: the call graph has a cycle). -/
def stackB (I : LinkInput) : Option Nat := (stackR I I.results).map (·.2)

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

theorem stackB_some {I : LinkInput} {S : Nat} (hS : stackB I = some S) :
    budOkW I I.results (bud I) = true ∧
      S = (progOf I.results).funcs.foldl (fun x g => max x (stackFn I g)) 0 := by
  unfold stackB at hS
  cases h : stackR I I.results with
  | none => rw [h] at hS; cases hS
  | some p =>
    obtain ⟨b, S'⟩ := p
    rw [h] at hS
    cases hS
    have hb : bud I = b := by funext g; simp [bud, h]
    unfold stackR at h
    dsimp only at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by rw [hb]; exact hok, ?_⟩
      simp only [stackFn, hb]
    · cases h

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
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and, Bool.or_eq_true,
        List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩

/-- **Soundness of the budget check**: under `okB`, `bud I` is a depth-independent budget of the
linked system of the input (whatever the base environment). -/
theorem budget_of {I : LinkInput} (hI : okB I = true) {S : Nat} (hS : stackB I = some S)
    (B : BaseEnv) (F : BitVec 64 → Prop) : (LinkSys.ofInput I B F).Budget fun _ g => bud I g := by
  intro _ g hg h hc
  have hh : h ∈ (progOf I.results).funcs := (LinkSys.ofInput I B F).callee_mem hc
  have hall := (stackB_some hS).1
  have he := edgeB_of_callee hI hg hc
  simp only [edgeB] at he
  simp only [budOkW, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hall
  rcases hall g hg h hh with he' | hle
  · rw [he] at he'; cases he'
  · exact hle

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

/-- **Every function of an input that passes the checker and the stack check** refines at every
fuel with the stack bound `stackFn I f ≤ S` (`stackFn_le`). -/
theorem crate_correct_stack {I : LinkInput} (hI : okB I = true) {S : Nat}
    (hS : stackB I = some S) (n : String) : StackStmt I n :=
  fun B F hB hFI _ hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program_stack _ (okB_sound hI hB hFI) (bud I)
      (budget_of hI hS B F) (Clif.Program.func?_some hf).1 M hent hroom hgfree hFeq
      himg hbe hargs hcs hsav hrel hpl htr

end StackBound

end E2E
