import FV.Backend.Proof.DeadCleanupSem

/-! Witnesses for #1117: the cleanup removes the scalar `fneg` that Cranelift's `fma` rules fold
into `fmsub`/`fnmsub`/`fnmadd` (`isa/aarch64/lower.isle`; Cranelift never lowers it, its result
having no use, `machinst/lower.rs`), and keeps an `fneg` whose result is read. Shape:
Cranelift's `runtests/fma.clif` `%fmsub_f64` (`fma v0, v1, (fneg v2)` → `fnmsub d0, d0, d1, d2`). -/

namespace Backend.DeadCleanup
open Backend.Proof

private def fnegDead : MInst := .fpuRR .neg .size64 (.vreg 3 .float) (.vreg 2 .float)
private def fnmsub : MInst :=
  .fpuRRRR .nMSub .size64 (.vreg 4 .float) (.vreg 0 .float) (.vreg 1 .float) (.vreg 2 .float)
private def retF : MInst := .rets [(.vreg 4 .float, .v 0)]
private def retBoth : MInst := .rets [(.vreg 4 .float, .v 0), (.vreg 3 .float, .v 1)]

/-- The scalar `fneg` is a flag-free producer; `fabs`/`fsqrt`/`fcvt` stay outside. -/
example : pureForm fnegDead = true ∧ flagFree fnegDead = true ∧
    pureForm (.fpuRR .abs .size64 (.vreg 3 .float) (.vreg 2 .float)) = false := ⟨rfl, rfl, rfl⟩

/-- Its specification keeps the world and continues. -/
example (a : BitVec 128) (w : Arm.ArmState) : ∃ outs, mspec 0 fnegDead [a] w = some (outs, w, .next) :=
  ⟨_, rfl⟩

/-- From a world whose flags a compare wrote it steps alike (it reads no flags). -/
example (a : BitVec 128) (p : Arm.PState) (w : Arm.ArmState) :
    mspec 0 fnegDead [a] (Arm.write_pstate p w) =
      (mspec 0 fnegDead [a] w).map (fun r => (r.1, Arm.write_pstate p r.2.1, r.2.2)) :=
  mspec_flagFree_pstate rfl p w

/-- The folded `fneg` goes: `fnmsub` alone, as stock emits. -/
example : (scan 5 [fnegDead, fnmsub, retF] []).1 = [fnmsub, retF] := by decide

/-- An `fneg` whose result is returned stays. -/
example : (scan 5 [fnegDead, fnmsub, retBoth] []).1 = [fnegDead, fnmsub, retBoth] := by decide

/-- The production pass (`prune`) on the whole function. -/
example : ∃ vc : VCode, (prune vc).blocks[0]!.insts.toList = [fnmsub, retF] := by
  refine ⟨⟨"fmsub_f64", #[⟨0, #[fnegDead, fnmsub, retF], #[], #[]⟩],
    #[.float, .float, .float, .float, .float], 0, 0, #[], #[], none⟩, ?_⟩
  decide +kernel

end Backend.DeadCleanup
