import FV.E2E.LinkArmRetOkZero

/-!
# `RetOkPRB κ M` at every depth (SEM1 #537, #680 (3))

Under `NeedSlots` (where `ThmPRBRL` needs the slot-byte machinery; without it `thmPRBRL_of_thm`
applies) and the base scope conditions of `LinkArmRetOkZero` (`BaseRetOk`, `RetCount`), every
returning invocation of an activation's run under `envOfB M g c` keeps the valid addresses and
the symbols and its declarations agree on a return count:

* a base invocation: as at depth `0`;
* a program callee `h`: its whole-program run keeps the allocations (`runLoop_allocs`, base
  externs `Ok.baseKeepsAllocs`) and the symbols (`runLoop_symbols`, `BaseRetOk`).

The count is the CLIF results' (the call results are the declared returns since #587, an `sret`
callee's struct pointer is not one); `sigRets_length_of_abiMatch` stays for the ABI returns.

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
    -- the call results are the declared returns (#587): the count is the CLIF results'
    exact ⟨rvals.length, Nat.le_refl _, fun _ _ _ _ hl' => hl'.symm, fun _ _ _ _ hl' => hl'.symm⟩
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
        exact ⟨rvals.length, Nat.le_refl _, fun _ _ _ _ hl' => hl'.symm,
          fun _ _ _ _ hl' => hl'.symm⟩
    · cases hr

end LinkSys

end E2E
