module

public import FV.Backend.Proof.IselCtlTryInd
public import FV.Backend.Proof.LowerContractT

@[expose] public section

/-!
# Family Ctl over typed contexts: the unmatchability statements (S11e5 Stage C, slice 5)

The integer proofs (`termUnmatchable`, `branchExcludedUnmatchable`, `tryUnmatchable`,
`tryIndUnmatchable`) only read the rule formats and the terminator's data, never the context
invariant, so they hold verbatim over typed contexts (`CtxT`): `termUnmatchableT_program`,
`branchExcludedUnmatchableT_program`, `tryUnmatchableT_program`, `tryIndUnmatchableT_program`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **`TermUnmatchableT`**: no rule of `lower` other than 964/1037 matches a `return`/`trap` of
a typed context. -/
theorem termUnmatchableT_program : TermUnmatchableT program := by
  intro r hr hroot f ctx _ ti t data hrt hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_fmts r hr
  simp only [lowerFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

/-- **`BranchExcludedUnmatchableT`**: the `try_call` rules of `lower_branch` never match a branch
of a typed context. -/
theorem branchExcludedUnmatchableT_program : BranchExcludedUnmatchableT program := by
  intro r hr hroot f ctx _ ti t data targets hrt hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_fmts r hr
  simp only [branchFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩, h3⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

/-- **`TryUnmatchableT`**: no rule of `lower_branch` other than 1034/1035 matches a `try_call` of
a typed context. -/
theorem tryUnmatchableT_program : TryUnmatchableT program := by
  intro r hr hroot f ctx _ ti fn args et data targets hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_try_fmts r hr
  simp only [tryFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hlo, hhi⟩, h1⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨sig, items, ext, he, hx, hs⟩ := tryCallData_spec hd
    rw [tryCallData_eq he hx hs] at hd
    cases hd
    simp only [V.data.injEq] at hdat
    omega
  · cases hok

/-- **`TryIndUnmatchableT`**: no rule of `lower_branch` other than 1036 matches a
`try_call_indirect` of a typed context. -/
theorem tryIndUnmatchableT_program : TryIndUnmatchableT program := by
  intro r hr hroot f ctx _ ti callee args et data targets hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_tryInd_fmts r hr
  simp only [tryIndFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hlo, hhi⟩, h1⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨sig, items, he⟩ := tryCallIndData_spec hd
    rw [tryCallIndData_eq he] at hd
    cases hd
    simp only [V.data.injEq] at hdat
    omega
  · cases hok

end Backend.Proof
