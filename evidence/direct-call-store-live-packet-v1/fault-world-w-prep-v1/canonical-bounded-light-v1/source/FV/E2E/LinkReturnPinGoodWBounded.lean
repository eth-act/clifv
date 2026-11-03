import FV.E2E.LinkGoodBoundedW
import FV.E2E.LinkReturnPinGoodWProgram

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys) {modes : Clif.Function → ReturnPinMode}
variable {κ : Nat → Clif.Function → Nat}
set_option autoImplicit false
set_option Elab.async false

theorem runGoodB_of_traceW_return_pins (hL : L.OkReturnPins modes) [L.CrunOk] {M : Nat} (ihG : 0 < M → L.ThmGW κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : L.MachEntry κ M g F G ra s w₀) {n : Nat}
    (hgood : ∀ i < n, actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s (L.XMode modes κ M g F) (L.hooks M) (κ M g) G (GotV (L.A g).vcp)
      (runX (L.mach M g) i s)) :
    L.RunGoodLBW n M g s := by
  intro M' g' c' t hR herrt
  rcases hR with ⟨k, hk, hno, e1, e2, e3, e4⟩ | ⟨M0, k, h, e1, hk, hno, hcall, herr1, hR'⟩
  · subst M' g' c' t
    have hG : (L.actRLMode modes κ M g F G s).GoodXW (runX (L.mach M g) k s) := hgood k hk
    refine ⟨L.XMode modes κ M g F, κ M g, G, GotV (L.A g).vcp, rfl, hG, he.imgG, he.imgS, ?_⟩
    intro xr h hx hb
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.1.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
      rw [layout_sum hc.layout]; have := hL.fits g hg; omega
    have hx' : insnAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) k s)) = some x := by
      rw [hpc]; exact insnAt_line hsz hj'
    rw [hx'] at hx; cases hx
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach M g) k s))
        (Arm.r .PC (runX (L.mach M g) k s)) = some (.blr xr) := by
      rw [hpc]; exact insnAt_ofLine_return_pins hc.layout hlm (by have := hL.fits g hg; omega) hG.1.prog hj'
    exact L.blrTo_of_pre_return_pins hL hg he (hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨xr, rfl⟩)) hG.1.prog hins hb
  · subst M
    have hG : (L.actRLMode modes κ (M0 + 1) g F G s).GoodXW (runX (L.mach (M0 + 1) g) k s) := hgood k hk
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.1.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach (M0 + 1) g) k s))
        (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) = some x := by
      rw [hpc]; exact insnAt_ofLine_return_pins hc.layout hlm (by have := hL.fits g hg; omega) hG.1.prog hj'
    have hpre : (L.actRLMode modes κ (M0 + 1) g F G s).CallPre (runX (L.mach (M0 + 1) g) k s) := by
      rcases hcall with ⟨n', hn', -⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inl ⟨n', rfl⟩)
      · rw [hins] at hr'; cases hr'; exact hG.1.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨r', rfl⟩)
    exact L.callGoodW_return_pins hL ihG hg he hpre hG.1.prog hcall _ _ _ _ hR' herrt


end LinkSys
end E2E
