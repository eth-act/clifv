import FV.E2E.LinkArmStage2Z

/-!
# Stage 2 at base calls, any depth (SEM1 #537, #680 (3), `docs/plans/uninit.md` §5.9)

`stage2Y_zero` at depth `0` uses only that every returning invocation is a base extern. At any
depth, a call whose CLIF invocation (of its count) is a base extern is answered by `Xb`, and every
instance of `CallPost` is that invocation (`InvokedN` is single-valued), so `Xb`'s result is
accepted (the base contracts `Ok.baseX`, `Ok.baseXI`).

* `envOfB_base_ret`: a returning extern of the restricted environment whose invocation is a base
  extern is the base's;
* `callPost_xb_base`, **`stage2Y_base`**, `stage2Z_base`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A returning extern of the restricted environment is the base's** when the invocations it
admits are of base externs. -/
theorem envOfB_base_ret {M : Nat} {g : Clif.Function} {c : BitVec 64}
    {A : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hG : ((L.envOfB M g c).only A).extern n = some G) {vals : List Clif.Val} {cm : Clif.Mem}
    {rvals : List Clif.Val} {cm' : Clif.Mem} (hr : G vals cm = .returned rvals cm')
    (hb : A n vals cm → L.P.func? n = none) :
    L.P.func? n = none ∧ ∃ G0, L.base.extern n = some G0 ∧ G0 vals cm = .returned rvals cm' := by
  obtain ⟨G1, hG1, rfl⟩ := Clif.Env.only_extern_eq hG
  obtain ⟨hA, hr'⟩ := onlyFn_returned hr
  have hpf := hb hA
  simp only [envOfB, hpf, Option.isSome_none, Bool.false_eq_true, false_and, ↓reduceIte,
    Clif.linkEnvR_none hpf] at hG1
  exact ⟨hpf, G1, hG1, hr'⟩

/-- **Every result of `Xb` is accepted** at a call whose invocation is a base extern. -/
theorem callPost_xb_base (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {M : Nat}
    (F : BitVec 64 → Prop) (c' c : BitVec 64) (A : String → List Clif.Val → Clif.Mem → Prop)
    (hb : ∀ n vals cm, A n vals cm → L.P.func? n = none)
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {x : List CV × Arm.ArmState}
    (hx : L.Xb.call d uses w = some x) :
    CallPost ((L.envOfB M g c').only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w x := by
  refine ⟨fun ext hin G sl cm args vals rvals cm' hG hd hargs hmr hret hlen => ?_,
    fun sig hs m G sl cm u args vals rvals cm' hdn hu hG _ hlo hargsS hmr hret hlen hty => ?_⟩
  · obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_base_ret hG hret (hb _ _ _)
    obtain ⟨outs, w', hx', h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G0 sl cm w d uses args vals rvals cm' hG0 hd
      hargs hmr hr0 hlen
    rw [hx] at hx'
    cases hx'
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, G0, hG0, hr0⟩ := L.envOfB_base_ret hG hret (hb _ _ _)
    subst hdn hu
    obtain ⟨outs, w', hx', h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hs m G0 sl cm w u args vals rvals
      cm' hG0 (fun _ h => by cases h) hlo hargsS hmr hr0 hlen hty
    rw [hx] at hx'
    cases hx'
    exact ⟨h1, h2, h3⟩

/-- **Stage 2 at a base call, any depth**: where the CLIF invocation of count `n` is a base extern
(every invocation of that count is), `XPRBT … n` answers `Xb`'s accepted result wherever
`CallPost` is not vacuous. -/
theorem stage2Y_base (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (c' : BitVec 64) (cs : Clif.State) (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat)
    (hb : ∀ nm vals m, InvokedN (L.envOfB M g c') L.P.bare cs n nm vals m → L.P.func? nm = none) :
    L.Stage2Y κ M g F P R (L.envOfB M g c') cs c Q n := by
  intro u w _ _ d uses hnv
  have hinst : ∃ n0, L.P.func? n0 = none ∧
      (d = some n0 ∨ d = none ∧ ∃ u args, uses = u :: args ∧ lo64 u = L.Xb.sym n0 0) ∧
      ∃ x, L.Xb.call d uses w = some x := by
    refine Classical.byContradiction fun hno => hnv fun r => ⟨fun ext hin G sl cm args vals rvals
      cm' hG hd hargs hmr hret hlen => ?_, fun sig hs m G sl cm u args vals rvals cm' hdn hu hG _
      hlo hargsS hmr hret hlen hty => ?_⟩
    · exfalso
      obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_base_ret hG hret (hb _ _ _)
      obtain ⟨outs, w', hx', -⟩ := hL.baseX g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
        (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G0 sl cm w d uses args vals rvals cm' hG0 hd
        hargs hmr hr0 hlen
      refine hno ⟨ext.name, hpf, ?_, _, hx'⟩
      rcases hd with ⟨rfl, -⟩ | ⟨rfl, -, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨rfl, _, args, rfl, lo64_ofX _⟩
    · exfalso
      obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_base_ret hG hret (hb _ _ _)
      subst hdn hu
      obtain ⟨outs, w', hx', -⟩ := hL.baseXI g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hs m G0 sl cm w u args vals rvals
        cm' hG0 (fun _ h => by cases h) hlo hargsS hmr hr0 hlen hty
      exact hno ⟨m, hpf, .inr ⟨rfl, u, args, rfl, hlo⟩, _, hx'⟩
  obtain ⟨n0, hpf, hshape, x, hx⟩ := hinst
  refine ⟨x, ?_, L.callPost_xb_base hL hg F c' c _ hb hx⟩
  rcases hshape with rfl | ⟨rfl, u, args, rfl, hlo⟩
  · rw [L.XPRBT_base hpf]; exact hx
  · rw [L.XPRBT_none (by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hlo]; exact (L.find_sym hL n0).2 hpf)]
    exact hx

theorem stage2Z_base (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (c' : BitVec 64) (cs : Clif.State) (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat)
    (hb : ∀ nm vals m, InvokedN (L.envOfB M g c') L.P.bare cs n nm vals m → L.P.func? nm = none) :
    L.Stage2Z κ M g F P R (L.envOfB M g c') cs c Q n :=
  Stage2Y.toZ L (L.stage2Y_base hL hg F P R c' cs c Q n hb)

end LinkSys

end E2E
