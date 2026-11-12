import FV.E2E.StackBound
import FV.E2E.LinkCheckT
import FV.E2E.LinkArmT

/-! # Typed copies of `FV.E2E.StackBound` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.StackBound` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_program` with a fixed stack bound for the entry**: with a budget `κ`
(`LinkSys.Budget`) that is `b` at the entry function `f` at every depth, every run of every fuel
`M` refines, provided the entry `sp` has `frameDrop f + b` bytes below it (without wrapping)
holding no code of the program, and the addresses outside the world are that stack and the code
(`hF`). -/
theorem backend_correct_program_stackT (L : LinkSys) (hL : L.OkT) {κ : Nat → Clif.Function → Nat}
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
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have hd := L.frameDrop_eqT hL hf
  have hres : StackAvail b (L.A f).af s := by
    refine ⟨?_, by rw [← hb M]; exact hκ.2 M f hf⟩
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetT L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel
    hpl htr
namespace LinkSys
end LinkSys
namespace StackBound
open LinkCheck

/-- Under `okB`, a callee of the linked system is an edge of the call graph. -/
theorem edgeB_of_calleeT {I : LinkInput} (hI : okBT I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (LinkSys.ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  have hdecl : ∀ e ∈ g.externs, e.2.name = h.name → edgeB (fun n => I.syms.lookup n) g h = true :=
    fun e he hn => by
      simp only [edgeB, edgeW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨e, he, hn⟩
  rcases hc with ⟨info, hs, n, hd, hpf⟩ | ⟨e, he, hpf⟩ | hc
  · have hpf' : (progOf I.results).func? n = some h := hpf
    obtain ⟨⟨e, he, hen⟩, -⟩ := siteOk_sound (site_sound (factsT hI hg).sites hs) hd hpf'
    exact hdecl e he (by rw [hen, (Clif.Program.func?_some hpf').2])
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hdecl e' he' (Clif.Program.func?_some (p := progOf I.results) hpf).2.symm
  · obtain ⟨hh, hmay⟩ := hc
    rcases hmay with hm | ⟨hnf, hsy, hsig⟩
    · obtain ⟨e, he, hen⟩ := List.mem_map.1 hm
      exact hdecl e he hen
    · obtain ⟨sig, hsm, hm⟩ := hsig h (func?_of_mem (okB_namesT hI) hh)
      have hsy' : (I.syms.lookup h.name).isSome = true := by
        revert hsy; show I.syms.lookup h.name ≠ none → _
        cases I.syms.lookup h.name <;> simp
      simp only [edgeB, edgeW, indFreeB_false hnf, hsy', Bool.not_false, Bool.true_and,
        Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact .inr ⟨sig, hsm, hm⟩
section
variable {fd : Array Nat} {succ : Array (List Nat)} {b₀ : Array (Option Nat)}
end

/-- **`goodN` is the input condition**: under `okB`, the function named `n` has a budget iff it
is a function of the program from which no call cycle is reachable. -/
theorem goodN_iffT {I : LinkInput} (hI : okBT I = true) {n : String} :
    goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ CycleFrom (Calls I I.results) f := by
  unfold goodN
  cases hf : (progOf I.results).func? n with
  | none => simp
  | some f =>
    simp only [Option.some.injEq, exists_eq_left']
    exact budC_isSome_iff (okB_namesT hI) (Clif.Program.func?_some hf).1

/-- **Soundness of the budgets**: under `okB`, `budMap`'s budgets (which meet `budOkW`,
`budOkW_budMap`), completed by the depth budget for the functions without one
(`LinkSys.hybrid`), are a budget of the linked system of the input (whatever the base
environment). -/
theorem budget_ofT {I : LinkInput} (hI : okBT I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (LinkSys.ofInput I B F).Budget ((LinkSys.ofInput I B F).hybrid (budO I) (budMax I)) := by
  refine LinkSys.budget_hybrid _ _ _ (fun h hh => (factsT hI hh).depth) ?_ ?_
    fun g hg bg hbg => budC_probe (I := I) (R := I.results) (okB_namesT hI) hg hbg
  · intro g hg bg hbg h hcl
    have hok := budOkW_budMap (I := I) (R := I.results) (okB_namesT hI)
    have he := edgeB_of_calleeT hI hg hcl
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

/-- **`backend_correct_program_stack` for the function named `n`** of the linked system `L` of
the input `I`, every premise but `L.OkT`: for every fuel `M`, from an entry whose `sp` has
`stackFn I f` bytes below it (without wrapping) holding no code of the program, with the
addresses outside the world that stack and the code. -/
def ProgStmtST (L : LinkSys) (I : LinkInput) (n : String) : Prop :=
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
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

/-- **The crate's theorem with the stack bound** for its function named `n` (`CrateStmt` with
`ProgStmtST`). -/
def StackStmtT (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInput I B F) →
    (∀ a, (LinkSys.ofInput I B F).Img a → F a) → ProgStmtST (LinkSys.ofInput I B F) I n

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
checker refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackNT {I : LinkInput} (hI : okBT I = true) {n : String}
    (hn : goodN I n = true) : StackStmtT I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stackT _ (okB_soundT hI hB hFI) (budget_ofT hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
end StackBound
end E2E
