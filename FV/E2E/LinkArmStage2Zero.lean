import FV.E2E.LinkArmThmPRBROf

/-!
# Stage 2 at depth `0` (SEM1 #537, #680 (3), `Stage2PRB κ 0`)

At depth `0` the callee runs of the linked system never return (`CrunOk.zero`), so every
returning extern of an activation's environment `envOfB 0 g c` (also restricted, `Env.only`) is
a base extern (`envOfB_zero_ret`). Where `CallPost` of a call is not vacuous, an instance with a
base extern exists; the base contracts (`Ok.baseX`, `Ok.baseXI`) then give `Xb`'s result, which
every instance accepts (`Xb` is a function), and `XPRBT` answers `Xb`'s result at a base call
(`XPRBT_base`; through a pointer, `XPRBT_none`: the pointer is no function of `P`, `symInj` via
`find_sym`).

* `envOfB_zero_ret`, `callPost_xb_zero` (every `Xb` result is accepted at depth `0`);
* **`stage2Y_zero`**: `Stage2Y κ 0` at any states `Q`, for any count `n`;
* **`stage2PRB_zero`**: `Stage2PRB κ 0`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **At depth `0` every returning extern is a base extern** (program callee runs never return,
`CrunOk.zero`). -/
theorem envOfB_zero_ret [hR : L.CrunOk] {g : Clif.Function} {c : BitVec 64}
    {A : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hG : ((L.envOfB 0 g c).only A).extern n = some G) {vals : List Clif.Val} {cm : Clif.Mem}
    {rvals : List Clif.Val} {cm' : Clif.Mem} (hr : G vals cm = .returned rvals cm') :
    L.P.func? n = none ∧ ∃ G0, L.base.extern n = some G0 ∧ G0 vals cm = .returned rvals cm' := by
  obtain ⟨G1, hG1, rfl⟩ := Clif.Env.only_extern_eq hG
  have hr' : G1 vals cm = .returned rvals cm' := by
    unfold Clif.onlyFn at hr
    split at hr
    · exact hr
    · cases hr
  cases hpf : L.P.func? n with
  | none =>
    simp only [envOfB, hpf, Option.isSome_none, Bool.false_eq_true, false_and, ↓reduceIte,
      Clif.linkEnvR_none hpf] at hG1
    exact ⟨rfl, G1, hG1, hr'⟩
  | some h =>
    exfalso
    simp only [envOfB, hpf, Option.isSome_some, true_and, Clif.linkEnvR_some hpf,
      Option.map_some] at hG1
    split at hG1
    · cases hG1
    · simp only [↓reduceIte, Option.some.injEq] at hG1
      subst hG1
      simp only at hr'
      split at hr'
      · split at hr'
        · exact hR.zero _ _ _ hr'
        · cases hr'
        · cases hr'
      · cases hr'

/-- **At depth `0` every result of `Xb` is accepted** by the call's `CallPost`. -/
theorem callPost_xb_zero (hL : L.Ok) [L.CrunOk] {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (F : BitVec 64 → Prop) (c' c : BitVec 64) (A : String → List Clif.Val → Clif.Mem → Prop)
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {x : List CV × Arm.ArmState}
    (hx : L.Xb.call d uses w = some x) :
    CallPost ((L.envOfB 0 g c').only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w x := by
  refine ⟨fun ext hin G sl cm args vals rvals cm' hG hd hargs hmr hret hlen => ?_,
    fun sig hs m G sl cm u args vals rvals cm' hdn hu hG _ hlo hargsS hmr hret hlen hty => ?_⟩
  · obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_zero_ret hG hret
    obtain ⟨outs, w', hx', h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G0 sl cm w d uses args vals rvals cm' hG0 hd
      hargs hmr hr0 hlen
    rw [hx] at hx'
    cases hx'
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, G0, hG0, hr0⟩ := L.envOfB_zero_ret hG hret
    subst hdn hu
    obtain ⟨outs, w', hx', h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hs m G0 sl cm w u args vals rvals
      cm' hG0 (fun _ h => by cases h) hlo hargsS hmr hr0 hlen hty
    rw [hx] at hx'
    cases hx'
    exact ⟨h1, h2, h3⟩

/-- **Stage 2 at depth `0`**: where `CallPost` of the invocation of count `n` is not vacuous, the
call is a base call and `XPRBT … n` answers `Xb`'s accepted result. -/
theorem stage2Y_zero (hL : L.Ok) [L.CrunOk] {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (c' : BitVec 64) (cs : Clif.State) (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat) :
    L.Stage2Y κ 0 g F P R (L.envOfB 0 g c') cs c Q n := by
  intro u w _ _ d uses hnv
  have hinst : ∃ n0, L.P.func? n0 = none ∧
      (d = some n0 ∨ d = none ∧ ∃ u args, uses = u :: args ∧ lo64 u = L.Xb.sym n0 0) ∧
      ∃ x, L.Xb.call d uses w = some x := by
    refine Classical.byContradiction fun hno => hnv fun r => ⟨fun ext hin G sl cm args vals rvals
      cm' hG hd hargs hmr hret hlen => ?_, fun sig hs m G sl cm u args vals rvals cm' hdn hu hG _
      hlo hargsS hmr hret hlen hty => ?_⟩
    · exfalso
      obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_zero_ret hG hret
      obtain ⟨outs, w', hx', -⟩ := hL.baseX g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
        (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G0 sl cm w d uses args vals rvals cm' hG0 hd
        hargs hmr hr0 hlen
      refine hno ⟨ext.name, hpf, ?_, _, hx'⟩
      rcases hd with ⟨rfl, -⟩ | ⟨rfl, -, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨rfl, _, args, rfl, lo64_ofX _⟩
    · exfalso
      obtain ⟨hpf, G0, hG0, hr0⟩ := L.envOfB_zero_ret hG hret
      subst hdn hu
      obtain ⟨outs, w', hx', -⟩ := hL.baseXI g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hs m G0 sl cm w u args vals rvals
        cm' hG0 (fun _ h => by cases h) hlo hargsS hmr hr0 hlen hty
      exact hno ⟨m, hpf, .inr ⟨rfl, u, args, rfl, hlo⟩, _, hx'⟩
  obtain ⟨n0, hpf, hshape, x, hx⟩ := hinst
  refine ⟨x, ?_, L.callPost_xb_zero hL hg F c' c _ hx⟩
  rcases hshape with rfl | ⟨rfl, u, args, rfl, hlo⟩
  · rw [L.XPRBT_base hpf]; exact hx
  · rw [L.XPRBT_none (by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hlo]; exact (L.find_sym hL n0).2 hpf)]
    exact hx

/-- **`Stage2PRB κ 0`.** -/
theorem stage2PRB_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRB κ 0 :=
  fun _ hg F _ cs w₀ _ _ _ s _ _ _ _ n =>
    L.stage2Y_zero hL hg F (L.BP 0 _ s) (L.RP 0 _ s) (spv w₀) cs (spv w₀) _ n

end LinkSys

end E2E
