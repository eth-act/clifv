import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselTermFactsTy
import FV.Backend.Proof.LowerContractT

/-!
# Family Ctl over typed contexts: the `lower_branch` closure roots (S11e5 Stage C, slice 5)

`brif` (1132), `tbnz` (1137), `tbz` (1138), `jump` (1139), `br_table` (1140) over typed contexts
(`CtxT`), on branches whose integer operands are in integer positions (`TermIntPos`: the `brif`
condition, the `br_table` index; on a typed-scope function every terminator's,
`termIntPos_of`). The proofs are the integer ones (`IselCtlBranch`, `IselCtlBrif`, `IselCtlTbz`,
`IselCtlBrTable`) with `is_nonzero_cmp_okT`/`ExtOut.semT` on the integer-position operand,
`ctxInvT_clif`/`iconst_data_invT`, and the `band` operand tested by `tbz`/`tbnz` an integer vreg
by `CtxInvT.intOps`.

Result: `branchRulesCorrectT_program` (`BranchRulesCorrectT program`; `BranchRuleOkT` carries
`TermIntPos ctx t`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- **`jump`** (`rule_lower_3270`) over typed contexts. -/
theorem jump_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    BranchRuleOkT isem MR p rule_lower_3270 := by
  intro f ctx _ ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kJ := fun n (hn : 30 ≤ n) t s v s' h => aarch64_jump_ok hp (ctx := ctx) hc (n := n) (t := t)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3270) rfl hp.t2462 term_2462_kind hd hi hmatch
  cases t with
  | jump d =>
    rw [termData_jump] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_3270, ext_single_target_iff, ctor_branch_target_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_single_target_iff, ctor_branch_target_iff] at * <;> isel_destruct <;>
      subst_vars)
    have h661 := ‹ApplyInternal _ _ _ _ 46 661 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kJ _ (by omega) _ _ _ _ h661
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_jump] at hmi
    cases hmi
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    exact ⟨_, by simp [LState.emit], jump_termOk hR hMR⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`lower_brif`** (`rule_lower_3231`) over typed contexts, on an integer-position condition. -/
theorem brif_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    BranchRuleOkT isem MR p rule_lower_3231 := by
  intro f ctx hctxT ti t data targets hd hi _ hip _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  have hctx := hctxT.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 100 ≤ n) c P (hsh : CondShape c P) a b s v s' h =>
    br_cond_result_ok hp (ctx := ctx) hc (n := n) (c := c) (P := P) (a := a) (b := b) (s := s)
      (v := v) (s' := s') hn hsh h
  have kNZ := fun n (hn : 300 ≤ n) x (hxi : IntPos ctx x) s c s' hvb h =>
    is_nonzero_cmp_okT hp hc (F := F) hR hctx (n := n) hn (x := x) hxi (s := s) (c := c)
      (s' := s') hvb h
  have hf := ruleFmt_term hp (r := rule_lower_3231) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    have hxi : IntPos ctx x := hip x (by simp [Compile.termIntOperands])
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3231] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    have h650 := ‹ApplyInternal _ _ _ _ 123 650 _ _ _ _›
    obtain ⟨ms0, hfr, hsh, hsem⟩ := kNZ _ (by omega) _ hxi _ _ _ hvb h650
    have h722 := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kB _ (by omega) _ _ hsh _ _ _ _ _ h722
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    rcases hsh with ⟨k, i, sz, rfl, hsz, -⟩ | ⟨k, i, sz, rfl, hsz, -⟩ |
      ⟨mi, mm, cond, rfl, hmi, -, -, hdm, -⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_zero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      refine ⟨ms0 ++ [_], ?emit, brif_termOk_gen hR hMR hfr (operands_condBr_zero _ _ k sz) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append hus ?_, fun w => ?_⟩
      · intro mm hmm u hu
        simp only [List.mem_singleton] at hmm
        subst hmm
        have hu' : u = k := by
          simp only [vuseNums, operands_condBr_zero] at hu
          simpa [Operand.isUse] using hu
        subst hu'
        exact condShape_zero_P hsh'
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        exact ⟨ρ1, w1, h1, hw1, by
          rw [show vuses #[(⟨k, .int, .use, .early, .reg⟩ : Operand)] ρ1 = [ρ1 k] from rfl,
            condBrHolds_zero]
          exact condSem_zero hsz hcs⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_notZero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      refine ⟨ms0 ++ [_], ?emit, brif_termOk_gen hR hMR hfr (operands_condBr_notZero _ _ k sz) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append hus ?_, fun w => ?_⟩
      · intro mm hmm u hu
        simp only [List.mem_singleton] at hmm
        subst hmm
        have hu' : u = k := by
          simp only [vuseNums, operands_condBr_notZero] at hu
          simpa [Operand.isUse] using hu
        subst hu'
        exact condShape_notZero_P hsh'
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        exact ⟨ρ1, w1, h1, hw1, by
          rw [show vuses #[(⟨k, .int, .use, .early, .reg⟩ : Operand)] ρ1 = [ρ1 k] from rfl,
            condBrHolds_notZero]
          exact condSem_notZero hsz hcs⟩
    · obtain ⟨m1, m2, hs3, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
      rw [hmi] at hm1
      cases hm1
      rw [ofV_condBr_cond] at hm2
      cases hm2
      simp only at hs2 hs3
      rw [hs3, hs2]
      have hf1 := hfr.append (Frag.emit_nodef _ hdm)
      refine ⟨(ms0 ++ [mm]) ++ [_], ?emit, brif_termOk_gen hR hMR hf1 (operands_condBr_cond _ _ cond) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append (UsesLo.append hus ?_) ?_, fun w => ?_⟩
      · intro m' hm' u hu
        simp only [List.mem_singleton] at hm'
        subst hm'
        exact condShape_cond_P hmi hsh' u hu
      · intro m' hm' u hu
        simp only [List.mem_singleton] at hm'
        subst hm'
        simp [vuseNums, operands_condBr_cond] at hu
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        obtain ⟨ps, hps, hb⟩ := condSem_cond hmi hcs
        obtain ⟨ρ2, w2, h2, hw2, -, hcond⟩ := Runs.flags hR hps w1
        exact ⟨ρ2, w2, seqRun_append_fall' isem h1 h2, hw2.trans hw1, by
          simp only [condBrHolds]
          rw [hcond, hb]⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbnz`** (`rule_lower_3251`) over typed contexts: the tested value is the integer operand
of a `band`. -/
theorem tbnz_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    BranchRuleOkT isem MR p rule_lower_3251 := by
  intro f ctx hctxT ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  have hctx := hctxT.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbnz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3251) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3251, ctor_tcbc_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj1⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi1⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInvT_clif hctx hj1 hi1
    obtain ⟨hd1⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    have hai : IntPos ctx a := hctx.intOps _ _ _ hi1 hcl1 a (by simp [intArgs])
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj2⟩ : Nonempty (ctx.defInst? b = some _) := ⟨‹_›⟩
    obtain ⟨hd2⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨hi2⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_invT hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hta⟩ : Nonempty (ctx.valueType? a = some _) := ⟨‹_›⟩
    obtain ⟨htc⟩ : Nonempty (tcbc _ _ = some _) := ⟨‹_›⟩
    have hra := hctx.valueReg_int ‹ctx.valueReg? a = some _› hai
    subst hra
    have h667 := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h667
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_nz] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨_, by simp [LState.emit], tbnz_termOk hR hMR hj1 hi1 hcl1 hj2 hi2 hcl2 he2 hta htc⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbz`** (`rule_lower_3257`) over typed contexts: the `icmp eq … (iconst 0)` look-through,
the tested value the integer operand of a `band`. -/
theorem tbz_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    BranchRuleOkT isem MR p rule_lower_3257 := by
  intro f ctx hctxT ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  have hctx := hctxT.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3257) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3257, ctor_tcbc_iff, ext_fits_in_64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj0⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi0⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl0, hcl0, hdat0⟩ := ctxInvT_clif hctx hj0 hi0
    obtain ⟨hd0⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
    rw [← hd0] at hdat0
    obtain ⟨cc, tyc, c, z, rfl, rfl, hcc⟩ := instData_icmp_inv hdat0
    have hcc' : cc = .eq := by cases cc <;> simp_all [ccIdx]
    subst hcc'
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨j1, hj1, info1, hi1, hd1⟩ : ∃ j, ctx.defInst? c = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 2 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨j3, hj3, info3, hi3, hd3⟩ : ∃ j, ctx.defInst? z = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty3, imm0, rfl, he3, hcl3⟩ := iconst_data_invT hctx hj3 hi3 hd3
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInvT_clif hctx hj1 hi1
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    have hai : IntPos ctx a := hctx.intOps _ _ _ hi1 hcl1 a (by simp [intArgs])
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hz0⟩ : Nonempty ((0 : Int) = (u64 (imm64OfIconst ty3 imm0) : Int)) := ⟨‹_›⟩
    obtain ⟨j2, hj2, info2, hi2, hd2⟩ : ∃ j, ctx.defInst? b = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_invT hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hta⟩ : Nonempty (ctx.valueType? a = some _) := ⟨‹_›⟩
    obtain ⟨htc⟩ : Nonempty (tcbc _ _ = some _) := ⟨‹_›⟩
    have hra := hctx.valueReg_int ‹ctx.valueReg? a = some _› hai
    subst hra
    have h668 := ‹ApplyInternal _ _ _ _ 46 668 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h668
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_z] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨_, by simp [LState.emit], tbz_termOk hR hMR hj0 hi0 hcl0 hj1 hi1 hcl1 hj2 hi2 hcl2 he2
      hj3 hi3 hcl3 he3 hz0 hta htc⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 8000000 in
/-- **`br_table`** (`rule_lower_3277`) over typed contexts, on an integer-position index. -/
theorem brTable_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    BranchRuleOkT isem MR p rule_lower_3277 := by
  intro f ctx hctxT ti t data targets hd hi hbt hip htl cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb _ hmatch heval
  have hctx := hctxT.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kZ := fun n (hn : 40 ≤ n) x s v s' h => zext32_ok hp (ctx := ctx) hc (n := n)
    (x := x) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' hk hr h => br_table_impl_ok hp (ctx := ctx) hc hR
    (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn hk hr h
  have hf := ruleFmt_term hp (r := rule_lower_3277) rfl hp.t2451 term_2451_kind hd hi hmatch
  cases t with
  | brTable x dc tbl =>
    have hxi : IntPos ctx x := hip x (by simp [Compile.termIntOperands])
    rw [termData_brTable] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3277, ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at * <;> isel_destruct <;> subst_vars)
    rename LState => st
    obtain ⟨⟨wx, hwx, hTx⟩, htbl⟩ := hbt _ _ _ rfl
    have hlen := htl _ _ _ rfl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have h669 := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kI _ (by omega) _ _ _ _ h669
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kS _ (by omega) _ _ _ _ h243
    rw [show ∀ n : Nat, (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) from
      fun n => by push_cast; omega, ofV_emitIsland] at hmi
    cases hmi
    have h556 := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
    have hext := kZ _ (by omega) _ _ _ _ h556
    rw [hs2, hs1] at hext
    obtain ⟨k, msx, rfl, hFx, hkl, hkx, hxsem⟩ := ExtOut.semT hR hctx hxi
      (pass := [.int 32, .int 64]) (by exact hvb) (.inl rfl) (by simp) (fun _ => by simp) hext
    have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
    have hJ := kB _ (by omega) _ _ _ _ _ _ _ (by omega) hkl h670
    simp only at hJ
    obtain ⟨ms0, st2, t1, t2, hF0, rfl, ht1, ht2, hu0, hr0⟩ := hJ
    have hFall := ((Frag.emit_nodef _ (m := .emitIsland _) rfl).append hFx).append hF0
    have hm1 := hFx.mono
    have hm0 := hF0.mono
    refine ⟨_, ?emit, brTable_termOk_gen hR hMR hFall (by dsimp only [LState.emit] at hm1 ht1 ⊢; omega)
      (by dsimp only [LState.emit] at hm1 ht2 ⊢; omega) hlen fun fr ρ v hvh hdfg hreg => ?_⟩
    case emit => simp [LState.emit, hFall.emitted]
    obtain ⟨hux, hrx⟩ := hxsem fr ρ v (hvh _ _ hreg) hdfg hreg
    have hkok : st.nextVreg ≤ k ∨ (fr.regs k).isSome := by
      rcases hkx with h | rfl
      · exact .inl (by dsimp only [LState.emit] at h ⊢; exact h)
      · exact .inr (by simp [hreg])
    refine ⟨?_, fun w => ?_⟩
    · intro mm hmm u hu
      simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hmm
      rcases hmm with rfl | hmm | hmm | rfl
      · simp [vuseNums, operands_emitIsland] at hu
      · exact hux mm hmm u hu
      · rcases hu0 mm hmm u hu with h | rfl
        · exact .inl (by dsimp only [LState.emit] at hm1 hm0 h ⊢; omega)
        · exact hkok
      · rw [vuseNums_jtSeq, List.mem_singleton] at hu
        subst hu; exact hkok
    · have hty := hdfg.2 x _ v hTx hreg
      have hvw : v.ty.width = wx := by rw [← ofClif_bits, hty]; rfl
      rw [List.append_assoc]
      refine Runs.append (P := fun ρ1 _ => ρ1 = ρ)
        (Runs.one hR (operands_emitIsland _) (by rfl) rfl (SameWorldNF.refl F w)
          fun _ _ => vdefUpd_nil _ _) ?_
      rintro ρ1 w1 rfl
      refine Runs.append (hrx w1) ?_
      rintro ρ2 w2 ⟨-, hex⟩
      refine (hr0 ρ2 w2).imp ?_
      rintro ρ3 w3 - ⟨h3, hhs⟩
      have hx32 := hex (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hx32
      have hv : ((lo64 (ρ2 k)).setWidth 32).toNat = v.toNat := by
        rw [hx32, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
        · rfl
        · exact Nat.lt_of_lt_of_le v.bits.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      refine ⟨by rw [hhs, hv, hlen], by rw [h3, hv]⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 400000 in
/-- **`BranchRulesCorrectT`**: the closure root rules of `lower_branch` — `brif` (1132), `tbnz`
(1137), `tbz` (1138), `jump` (1139), `br_table` (1140) — are correct over typed contexts (on
branches whose integer operands are in integer positions, `TermIntPos`). -/
theorem branchRulesCorrectT_program : BranchRulesCorrectT program := by
  intro F isem MR hR hMR r hr hroot
  rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr
  simp only [R.lower_branch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hroot (by decide +kernel)
  · exact tbnz_ruleOkT data_program hR hMR
  · exact tbz_ruleOkT data_program hR hMR
  · exact absurd hroot (by decide +kernel)
  · exact absurd hroot (by decide +kernel)
  · exact brif_ruleOkT data_program hR hMR
  · exact jump_ruleOkT data_program hR hMR
  · exact brTable_ruleOkT data_program hR hMR

end Backend.Proof
