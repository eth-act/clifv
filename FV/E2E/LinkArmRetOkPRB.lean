import FV.E2E.LinkArmRetOkZero

/-!
# `RetOkPRB κ M` at every depth (SEM1 #537, #680 (3))

Under `NeedSlots` (where `ThmPRBRL` needs the slot-byte machinery; without it `thmPRBRL_of_thm`
applies) and the base scope conditions of `LinkArmRetOkZero` (`BaseRetOk`, `RetCount`), every
returning invocation of an activation's run under `envOfB M g c` keeps the valid addresses and
the symbols and its declarations agree on an ABI return count:

* a base invocation: as at depth `0`;
* a program callee `h`: its whole-program run keeps the allocations (`runLoop_allocs`, base
  externs `Ok.baseKeepsAllocs`) and the symbols (`runLoop_symbols`, `BaseRetOk`), and every
  declaration of `h` in `g` is `h`'s signature (`Ok.declSig`) while every indirect call
  signature that can enter `h` matches it (`abiMatch`), so they agree on `sigRets`
  (`sigRets_length_of_abiMatch`).

**`retOkPRB_of`**: `RetOkPRB κ M` for every `M`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem sigRets_length_eq (s : Clif.Signature) :
    (sigRets s).length =
      if s.params.any (·.purpose == .sret) && s.returns.isEmpty then 1 else s.returns.length := by
  unfold sigRets
  cases hf : s.params.find? (·.purpose == .sret) with
  | some p =>
    have ha : s.params.any (·.purpose == .sret) = true :=
      List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
    cases hr : s.returns.isEmpty <;> simp [ha]
  | none =>
    have ha : s.params.any (·.purpose == .sret) = false := by
      rw [List.find?_eq_none] at hf
      exact List.any_eq_false.mpr fun x hx => by simpa using hf x hx
    simp [ha]

/-- Signatures that `abiMatch` have the same number of ABI return registers. -/
theorem sigRets_length_of_abiMatch {d t : Clif.Signature} (h : d.abiMatch t = true) :
    (sigRets d).length = (sigRets t).length := by
  obtain ⟨-, h2, h3⟩ := Clif.Signature.abiMatch_eq_true.mp h
  have hl : d.returns.length = t.returns.length := by
    simpa [Clif.AbiParam.tys] using congrArg List.length h3
  have ha : d.params.any (·.purpose == .sret) = t.params.any (·.purpose == .sret) := by
    have := congrArg (fun l => l.any (· == Clif.ArgPurpose.sret)) h2
    simpa [Clif.AbiParam.purposes, List.any_map, Function.comp_def] using this
  have he : d.returns.isEmpty = t.returns.isEmpty := by
    cases hd : d.returns <;> cases ht : t.returns <;> simp_all
  rw [sigRets_length_eq, sigRets_length_eq, ha, hl, he]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`RetOkPRB κ M`** under `NeedSlots` and the base scope conditions. -/
theorem retOkPRB_of (hL : L.Ok) [hR : L.CrunOk] (hN : L.NeedSlots) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g) (M : Nat) : L.RetOkPRB κ M := by
  intro g hg F vals cs w₀ ini _ n nm vals' m G rvals cm' _ hG hr
  cases hpf : L.P.func? nm with
  | none =>
    -- a base invocation: as at depth `0`
    simp only [envOfB, hpf, Option.isSome_none, Bool.false_eq_true, false_and, ↓reduceIte,
      Clif.linkEnvR_none hpf] at hG
    obtain ⟨hv, hs⟩ := hB nm G hG vals' m rvals cm' hr
    refine ⟨hv, hs, ?_⟩
    have hmem := sigsOf_mem (g := g) (nm := nm)
    by_cases hex : ∃ s, ((∃ ext ∈ g.externs.map (·.2), ext.name = nm ∧ s = ext.sig) ∨
        s ∈ indSigs g) ∧ rvals.length = s.returns.length
    · obtain ⟨s, hs, hl⟩ := hex
      refine ⟨(sigRets s).length, hl ▸ returns_le_sigRets s, fun ext hext hnm hl' => ?_,
        fun sig hsg _ hl' => ?_⟩
      · exact hC g hg nm hpf ext.sig (hmem _ (.inl ⟨ext, hext, hnm, rfl⟩)) s (hmem s hs) (by omega)
      · exact hC g hg nm hpf sig (hmem _ (.inr hsg)) s (hmem s hs) (by omega)
    · refine ⟨rvals.length, Nat.le_refl _, fun ext hext hnm hl' => ?_, fun sig hsg _ hl' => ?_⟩
      · exact absurd ⟨ext.sig, .inl ⟨ext, hext, hnm, rfl⟩, hl'⟩ hex
      · exact absurd ⟨sig, .inr hsg, hl'⟩ hex
  | some h =>
    -- a program callee: its whole-program run
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig : (L.envOfB M g (spv w₀)).sigOf nm = some h.sig := by
      simp [envOfB, Clif.linkEnvR, hpf]
    simp only [envOfB, hpf, Option.isSome_some, true_and, Clif.linkEnvR_some hpf,
      Option.map_some] at hG
    split at hG
    · cases hG
    simp only [↓reduceIte, Option.some.injEq] at hG
    subst hG
    simp only at hr
    split at hr
    · rename_i hpl
      obtain ⟨ini', hpB⟩ := hpl hN
      cases hinit : Clif.initState L.P nm vals' m with
      | trap c' => rw [hinit] at hr; cases hr
      | stuck m' => rw [hinit] at hr; cases hr
      | ok cs' =>
        rw [hinit] at hr
        simp only at hr
        obtain ⟨N, hN'⟩ := hR.runs M cs' _ hr (.inl ⟨_, _, rfl⟩)
        have hE := clifEntry_initState (f := h) (by rw [hname]; exact hpf) (by rw [hname]; exact hinit)
        have hI : Clif.LInv L.P cs' := runInv_entry hh hE
        have hv := Clif.runLoop_allocs hL.free (hL.baseKeepsAllocs hN) N cs' rvals cm' hI
          (Clif.initState_allocInv hinit) hN'
        have hsy := Clif.runLoop_symbols hL.free
          (fun n' f hf vals m₁ rv m₂ hr' => (hB n' f hf vals m₁ rv m₂ hr').2) N cs' rvals cm' hI hN'
        have hsy0 := (L.initState_memB hpf hinit hpB).2.1
        refine ⟨hv, hsy.trans hsy0, ?_⟩
        by_cases hex : ∃ s, ((∃ ext ∈ g.externs.map (·.2), ext.name = nm ∧ s = ext.sig) ∨
            (s ∈ indSigs g ∧ s.abiMatch h.sig = true)) ∧ rvals.length = s.returns.length
        · obtain ⟨s, hs, hl⟩ := hex
          have hsR : (sigRets s).length = (sigRets h.sig).length := by
            rcases hs with ⟨ext, hext, hnm, rfl⟩ | ⟨-, hm⟩
            · rw [hL.declSig g hg ext hext h (hnm ▸ hpf)]
            · exact sigRets_length_of_abiMatch hm
          refine ⟨(sigRets h.sig).length, hsR ▸ hl ▸ returns_le_sigRets s,
            fun ext hext hnm _ => ?_, fun sig _ hsg _ => ?_⟩
          · rw [hL.declSig g hg ext hext h (hnm ▸ hpf)]
          · exact sigRets_length_of_abiMatch (hsg h.sig hsig)
        · refine ⟨rvals.length, Nat.le_refl _, fun ext hext hnm hl' => ?_,
            fun sig hsg hm hl' => ?_⟩
          · exact absurd ⟨ext.sig, .inl ⟨ext, hext, hnm, rfl⟩, hl'⟩ hex
          · exact absurd ⟨sig, .inr ⟨hsg, hm h.sig hsig⟩, hl'⟩ hex
    · cases hr

end LinkSys

end E2E
