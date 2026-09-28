import FV.Backend.Proof.IselCmpDiv

/-!
# Family C: division root rules
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The division instruction -/

set_option maxRecDepth 20000 in
theorem div_variantNames_Binary : (variantNames 152)[2]? = some "Binary" := rfl

theorem instData_div_inv {f : Clif.Function} {cl : Clif.Inst} {w : V} {ko : Nat} {op : Clif.DivOp}
    (hname : (variantNames 151)[ko]? = some (divOpcode op))
    (h : instData f cl = .ok (.data 152 2 [.data 151 ko [], w])) :
    ∃ ty x y, cl = .div op ty x y ∧ eTy ty = true ∧ w = .values [x, y] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [div_variantNames_Binary] at hf
  rw [hname] at ho
  cases cl <;> simp [instNames] at hf ho
  · rename_i op' _ _ _
    cases op <;> cases op' <;> simp [binaryOpcode, divOpcode] at ho
  · rename_i op' ty x y
    have : op' = op := by cases op <;> cases op' <;> simp [divOpcode] at ho ⊢
    subst this
    refine ⟨ty, x, y, rfl, ?_⟩
    simp only [instData] at h
    split at h
    · rename_i he
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨he, h3.2.1⟩
    · cases h

theorem getAs_ne_trap (fr : Clif.Frame) (x : Nat) (ty : Clif.Ty) (c : Clif.TrapCode) :
    fr.getAs x ty ≠ .trap c := by
  unfold Clif.Frame.getAs Clif.Frame.get
  cases fr.regs x with
  | none => simp [Clif.Res.ofOption, bind, Clif.Res.bind]
  | some v =>
    simp only [Clif.Res.ofOption, bind, Clif.Res.bind]
    cases v.as? ty <;> simp

theorem evalInst_div_inv {fr : Clif.Frame} {cm : Clif.Mem} {op : Clif.DivOp} {ty : Clif.Ty}
    {x y : Nat} {r : Clif.Res (List Clif.Val × Clif.Mem)} (h : Clif.evalInst fr cm (.div op ty x y) = r)
    (hr : ∀ m, r ≠ .stuck m) :
    ∃ a b, fr.regs x = some ⟨ty, a⟩ ∧ fr.regs y = some ⟨ty, b⟩ ∧
      r = Clif.Res.bind (Clif.Res.ofExcept (Clif.Sem.div op a b)) fun q => .ok ([⟨ty, q⟩], cm) := by
  simp only [Clif.evalInst] at h
  cases hx : fr.getAs x ty with
  | ok a =>
    cases hy : fr.getAs y ty with
    | ok b =>
      rw [hx, hy] at h
      exact ⟨a, b, getAs_ok hx, getAs_ok hy, by rw [← h]; rfl⟩
    | trap c => exact absurd hy (getAs_ne_trap _ _ _ _)
    | stuck m => rw [hx, hy] at h; subst h; exact absurd rfl (hr m)
  | trap c => exact absurd hx (getAs_ne_trap _ _ _ _)
  | stuck m => rw [hx] at h; subst h; exact absurd rfl (hr m)

/-- **`LowerInstOk` for a division**: the result's run when it returns, the halt at a trap
instruction with its code when it traps. -/
theorem lowerInstOk_div {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat}
    {results : List Nat} {st st' : LState} {ms : List MInst} {d : Nat} (hMR : MRStable F MR)
    (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg) (hd : st.nextVreg ≤ d)
    (hrun : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (w : Arm.ArmState) (a b : BitVec ty.width),
      fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr →
      fr.regs x = some ⟨ty, a⟩ → fr.regs y = some ⟨ty, b⟩ →
      UsesOk st fr ms ∧
      (∀ c, Clif.Sem.div op a b = .error c → TrapRun isem ms ρ w c) ∧
      (∀ q, Clif.Sem.div op a b = .ok q → Runs F isem ms ρ w (fun ρ' _ => VHolds ⟨ty, q⟩ (ρ' d)))) :
    LowerInstOk isem MR env cp ctx (.div op ty x y) results st [[.vreg d .int]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  have hev : instOutcome env cp fr cm (.div op ty x y) = Clif.evalInst fr cm (.div op ty x y) := rfl
  rw [hev]
  split
  · rename_i vals cm' ho
    obtain ⟨a, b, hxa, hyb, hr⟩ := evalInst_div_inv ho (fun m h => by cases h)
    obtain ⟨hu, -, hok⟩ := hrun fr ρ w a b hf hv hdfg hxa hyb
    cases hq : Clif.Sem.div op a b with
    | error c => rw [hq] at hr; cases hr
    | ok q =>
      rw [hq] at hr
      simp only [Clif.Res.ofExcept, Clif.Res.bind] at hr
      cases hr
      obtain ⟨ρ', w', hs, hw, hh⟩ := hok q hq
      refine ⟨hu, ρ', w', hs, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hw hmr⟩
      intro j rs val hrs hval
      match j, hrs, hval with
      | 0, hrs, hval =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
        subst hrs; subst hval
        exact ⟨d, .int, rfl, .inl hd, hh⟩
      | _ + 1, hrs, _ => simp at hrs
  · rename_i c ho
    intro _
    obtain ⟨a, b, hxa, hyb, hr⟩ := evalInst_div_inv ho (fun m h => by cases h)
    obtain ⟨hu, htr, -⟩ := hrun fr ρ w a b hf hv hdfg hxa hyb
    cases hq : Clif.Sem.div op a b with
    | error c' =>
      rw [hq] at hr
      simp only [Clif.Res.ofExcept, Clif.Res.bind] at hr
      cases hr
      obtain ⟨k, i, ops, ρ₁, w₁, outs, w₂, hs, hc⟩ := htr c hq
      exact ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hc⟩
    | ok q => rw [hq] at hr; simp [Clif.Res.ofExcept, Clif.Res.bind] at hr
  · trivial

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem udiv64_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1116 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  trace_state
  sorry

end Root

end Backend.Proof
