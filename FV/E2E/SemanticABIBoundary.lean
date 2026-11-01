import FV.E2E.CompiledSemanticABI

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

namespace CompiledSemanticABI
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- Both artifact variants retain the original physical argument boundary. -/
theorem entryRegs (hc : CompiledSemanticABI f k vc vcp rf af fa fb) :
    ∀ loc ∈ locsOf f.sig,∀ r,loc = .reg r → ∃ n,r = .x n ∧ n ≤ 8 := by
  cases hc with
  | compatible h => exact h.entryRegs
  | memorySretCopy family equal effects h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int family.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk family.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

end CompiledSemanticABI

/-- TLS provenance retains the previous source boundary. The new memory whitelist has no TLS. -/
theorem hasTls_of_vcode_semantic_abi {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledSemanticABI f k vc vcp rf af fa fb) (tls : vcp.hasTls = true) : hasTls f = true := by
  cases hc with
  | compatible h => exact hasTls_of_vcode_semantic h tls
  | @memorySretCopy cleanup result family equal effects h =>
    have raw := Stock.MemoryStoreCfg.effectsOnly_noTls effects
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at tls
    cases tls

set_option maxHeartbeats 1000000 in
/-- The original hardware ABI and actual frame allocation retain stack-argument avoidance. -/
theorem stackArgsAvoid_frameW_semantic_abi {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledSemanticABI f k vc vcp rf af fa fb) {K : Nat}
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail K af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  intro off v hm j hj hF
  have h := hargs _ _ hm
  simp only at h
  have hframe := lowerRFunc_frame hc.alloc
  have hfs := (lowerRFunc_ok hc.alloc).1.1
  have hD : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hframe]
  have hsz : (RAFrame.compute vcp rf).size ≤ af.frameSize := by
    have e : (RAFrame.compute vcp rf).total =
        alignTo ((RAFrame.compute vcp rf).size + vcp.slotBytes) 16 +
          clobberBytes rf.saved := rfl
    rw [hfs, e]
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (le_alignTo16 _))
      (Nat.le_add_right _ _)
  have hsp := hres.1
  have hfit := h.fits
  have hx : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j -
      (spv s - BitVec.ofNat 64 (frameDrop af))).toNat = off + j + frameDrop af := by
    rw [hD]
    bv_omega
  rcases hF with (⟨-, h2⟩ | ⟨-, h2⟩ | hcode) | ⟨hlt, -⟩
  · rw [hx] at h2; omega
  · rw [hx] at h2; omega
  · have e : spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j = spv s + BitVec.ofNat 64 (off + j) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [e] at hcode
    exact h.noCode j hj hcode
  · rw [(spBody_toNat hres).1] at hlt
    have : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = (spv s).toNat + off + j := by
      bv_omega
    omega



end E2E
