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
* `RetCount g`: the declarations of `g` of externs outside `P` and `g`'s indirect call signatures
  with the same number of returns have the same number of ABI return registers (`sigRets`);
  decidable (`retCountB`, `retCountB_sound`).

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

/-- The signatures a returning base invocation of `g` can stand for: its declarations of externs
outside `P` and its indirect call signatures. -/
def baseSigs (g : Clif.Function) : List Clif.Signature :=
  ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone).map (·.sig) ++ indSigs g

/-- **Return-count agreement** of the signatures a base invocation of `g` can stand for. -/
def RetCount (g : Clif.Function) : Prop :=
  ∀ s₁ ∈ L.baseSigs g, ∀ s₂ ∈ L.baseSigs g, s₁.returns.length = s₂.returns.length →
    (sigRets s₁).length = (sigRets s₂).length

def retCountB (g : Clif.Function) : Bool :=
  (L.baseSigs g).all fun s₁ => (L.baseSigs g).all fun s₂ =>
    s₁.returns.length != s₂.returns.length || (sigRets s₁).length == (sigRets s₂).length

theorem retCountB_sound {g : Clif.Function} (h : L.retCountB g = true) : L.RetCount g := by
  intro s₁ h₁ s₂ h₂ he
  have := List.all_eq_true.mp (List.all_eq_true.mp h s₁ h₁) s₂ h₂
  simpa [he] using this

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
  have hsig : (L.envOfB 0 g (spv w₀)).sigOf nm = none := by
    simp [envOfB, Clif.linkEnvR, hpf]
  -- the signatures the invocation can stand for are base signatures of `g`
  have hmem : ∀ s, ((∃ ext ∈ g.externs.map (·.2), ext.name = nm ∧ s = ext.sig) ∨ s ∈ indSigs g) →
      s ∈ L.baseSigs g := by
    rintro s (⟨ext, hext, hnm, rfl⟩ | hs)
    · refine List.mem_append_left _ (List.mem_map.mpr ⟨ext, List.mem_filter.mpr ⟨hext, ?_⟩, rfl⟩)
      simp [hnm, hpf]
    · exact List.mem_append_right _ hs
  by_cases hex : ∃ s, ((∃ ext ∈ g.externs.map (·.2), ext.name = nm ∧ s = ext.sig) ∨
      s ∈ indSigs g) ∧ rvals.length = s.returns.length
  · obtain ⟨s, hs, hl⟩ := hex
    refine ⟨(sigRets s).length, hl ▸ returns_le_sigRets s, fun ext hext hnm hl' => ?_,
      fun sig hsg _ hl' => ?_⟩
    · exact hC g hg ext.sig (hmem _ (.inl ⟨ext, hext, hnm, rfl⟩)) s (hmem s hs) (by omega)
    · exact hC g hg sig (hmem _ (.inr hsg)) s (hmem s hs) (by omega)
  · refine ⟨rvals.length, Nat.le_refl _, fun ext hext hnm hl' => ?_, fun sig hsg _ hl' => ?_⟩
    · exact absurd ⟨ext.sig, .inl ⟨ext, hext, hnm, rfl⟩, hl'⟩ hex
    · exact absurd ⟨sig, .inr hsg, hl'⟩ hex

/-- **`ThmPRBRL κ 0`** under the base scope conditions. -/
theorem thmPRBRL_zero_of (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g) : L.ThmPRBRL κ 0 :=
  L.thmPRBRL_zero hL hκ (L.retOkPRB_zero hB hC)

end LinkSys

end E2E
