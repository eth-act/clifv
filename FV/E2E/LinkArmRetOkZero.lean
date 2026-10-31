import FV.E2E.LinkArmCountZero

/-!
# `RetOkPRB κ 0` from a scope condition on the base externs (SEM1 #537, #680 (3))

`RetOkPRB` (`InvokedRetOk` of the activations' runs) asks every returning invocation to keep the
valid addresses and the symbols, and the declarations it can stand for to agree on an ABI return
count. At depth `0` every returning invocation is a base one (`envOfB_zero_ret`), so it is a fact
of the base externs and of the declarations of `g`; neither follows from `LinkSys.Ok` (no field
keeps the symbols when every function is `IndFree`, and two declarations of an extern outside
`P`, or an indirect call signature, may differ in their return registers). Scope conditions (new,
`Ok` unchanged):

* `BaseRetOk`: the returning base externs keep the valid addresses and the symbols;
* `RetCount g`: for every extern name outside `P`, `g`'s declarations of it and `g`'s indirect
  call signatures with the same numbers of parameters and of returns have the same number of ABI
  return registers (`sigRets`); decidable (`retCountB`, `retCountB_sound`). Only signatures with
  as many parameters as the invocation has values can stand for it (`InvokedRetOk`), so pairs of
  different parameter counts are not compared (#733: an `sret` `call_indirect` next to a `void`
  outside extern). Measured on fv-demo: holds for all 551 functions (397 with slots, 13 with
  indirect calls); the stronger form across different names fails on 3 (a base `sret` extern next
  to a `void` one).

**`retOkPRB_zero`**: `RetOkPRB κ 0` from both; **`thmPRBRL_zero_of`**: `ThmPRBRL κ 0` from both.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The returning base externs keep the valid addresses and the symbols.** -/
def BaseRetOk : Prop :=
  ∀ n G, L.base.extern n = some G → ∀ vals m rvals m', G vals m = .returned rvals m' →
    (∀ a k, m'.valid a k = true → m.valid a k = true) ∧ m'.symbols = m.symbols

/-- The signatures an invocation of the extern `nm` in `g` can stand for: `g`'s declarations
of `nm` and its indirect call signatures. -/
def sigsOf (g : Clif.Function) (nm : String) : List Clif.Signature :=
  ((g.externs.map (·.2)).filter (·.name == nm)).map (·.sig) ++ indSigs g

/-- The signatures agree on the number of ABI return registers per number of parameters and of
returns. -/
def agreeB (l : List Clif.Signature) : Bool :=
  l.all fun s₁ => l.all fun s₂ =>
    s₁.params.length != s₂.params.length || s₁.returns.length != s₂.returns.length ||
      (sigRets s₁).length == (sigRets s₂).length

/-- **Return-count agreement** of the signatures a base invocation of `g` can stand for (per
extern name outside `P`, per number of parameters, #733). -/
def RetCount (g : Clif.Function) : Prop :=
  ∀ nm, L.P.func? nm = none → ∀ s₁ ∈ sigsOf g nm, ∀ s₂ ∈ sigsOf g nm,
    s₁.params.length = s₂.params.length → s₁.returns.length = s₂.returns.length →
      (sigRets s₁).length = (sigRets s₂).length

def retCountB (g : Clif.Function) : Bool :=
  agreeB (indSigs g) &&
    (g.externs.map (·.2)).all fun e => (L.P.func? e.name).isSome || agreeB (sigsOf g e.name)

theorem agreeB_sound {l : List Clif.Signature} (h : agreeB l = true) : ∀ s₁ ∈ l, ∀ s₂ ∈ l,
    s₁.params.length = s₂.params.length → s₁.returns.length = s₂.returns.length →
      (sigRets s₁).length = (sigRets s₂).length := by
  intro s₁ h₁ s₂ h₂ hp he
  have := List.all_eq_true.mp (List.all_eq_true.mp h s₁ h₁) s₂ h₂
  simpa [hp, he] using this

theorem retCountB_sound {g : Clif.Function} (h : L.retCountB g = true) : L.RetCount g := by
  simp only [retCountB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Option.isSome_iff_ne_none, ne_eq] at h
  intro nm hpf
  by_cases hex : ∃ e ∈ g.externs.map (·.2), e.name = nm
  · obtain ⟨e, he, rfl⟩ := hex
    exact agreeB_sound ((h.2 e he).resolve_left (by simp [hpf]))
  · have hf : (g.externs.map (·.2)).filter (·.name == nm) = [] :=
      List.filter_eq_nil_iff.mpr fun e he hn => hex ⟨e, he, by simpa using hn⟩
    have : sigsOf g nm = indSigs g := by simp [sigsOf, hf]
    rw [this]
    exact agreeB_sound h.1

theorem sigsOf_mem {g : Clif.Function} {nm : String} (s : Clif.Signature)
    (h : (∃ ext ∈ g.externs.map (·.2), ext.name = nm ∧ s = ext.sig) ∨ s ∈ indSigs g) :
    s ∈ sigsOf g nm := by
  rcases h with ⟨ext, hext, hnm, rfl⟩ | hs
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨ext, List.mem_filter.mpr ⟨hext, by simp [hnm]⟩, rfl⟩)
  · exact List.mem_append_right _ hs

/-- A returning extern of `envOfB 0` is a base extern (`envOfB_zero_ret` without restriction). -/
theorem envOfB_zero_ret' [L.CrunOk] {g : Clif.Function} {c : BitVec 64} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.Outcome} (hG : (L.envOfB 0 g c).extern n = some G)
    {vals : List Clif.Val} {cm : Clif.Mem} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hr : G vals cm = .returned rvals cm') :
    L.P.func? n = none ∧ ∃ G0, L.base.extern n = some G0 ∧ G0 vals cm = .returned rvals cm' := by
  have hG' : ((L.envOfB 0 g c).only fun _ _ _ => True).extern n =
      some (Clif.onlyFn (fun _ _ _ => True) n G) := by
    rw [Clif.Env.only_extern, hG]; rfl
  exact L.envOfB_zero_ret hG' (by rw [Clif.onlyFn_of trivial]; exact hr)

/-- **`RetOkPRB κ 0`** from the scope conditions. -/
theorem retOkPRB_zero [L.CrunOk] (hB : L.BaseRetOk) (hC : ∀ g ∈ L.P.funcs, L.RetCount g) :
    L.RetOkPRB κ 0 := by
  intro g hg F vals cs w₀ ini _ n nm vals' m G rvals cm' _ hG hr
  obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_zero_ret' hG hr
  obtain ⟨hv, hs⟩ := hB nm G0 hG0 vals' m rvals cm' hr0
  refine ⟨hv, hs, ?_⟩
  -- the call results are the declared returns (#587): the count is the CLIF results'
  exact ⟨rvals.length, Nat.le_refl _, fun _ _ _ _ hl' => hl'.symm, fun _ _ _ _ hl' => hl'.symm⟩

/-- **`ThmPRBRL κ 0`** under the base scope conditions. -/
theorem thmPRBRL_zero_of (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g) : L.ThmPRBRL κ 0 :=
  L.thmPRBRL_zero hL hκ (L.retOkPRB_zero hB hC)

end LinkSys

end E2E
