import FV.Backend.Proof.IselPoolFree
import FV.Backend.Proof.FormsCoverCompleteT
import FV.Backend.Proof.DeadCleanupPrepare
import FV.E2E.SizeIn

/-!
# The typed scopes' prepared code has no literal-pool load (#1002)

On the float scope `LowerScopeTF` (hence on the typed scope `LowerScopeT`), `lowerFunction`'s
VCode has no literal-pool load: the scope's `f64const`s are `Compile.f64PoolFree`, so
`constant_f64`'s pool rule never fires (`Pool.stmt_noPool`, `Pool.termCall_noPool`,
`Pool.tryCall_noPool`), and the driver's own instructions, its renaming, `prepare` and the
dead-code cleanup add none. Hence `VCode.noPoolB` and the literal loads' reach `poolReachB` of the
prepared VCode are theorems on these scopes (`poolReachB_lowerTF`, `poolReachB_cleanup_lowerTF`,
`poolReachB_lowerT`, `poolReachB_cleanup_lowerT`), with no size condition, and the typed
analysis's three-way coverage is two-way there (`Driver.formsCovered2_of_noPool`,
`Driver.formsCovered2_completeT`; the float scope's is in `LinkScopeChecksTF`).

Since #955 these were a premise `hpool` of the typed scopes' size theorems and a run-time
conjunct of the input scopes; #1002 part 1 removes both.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## Literal-pool loads of the driver's instructions -/

theorem isLitLoad_of_ne {m : MInst} (h : ∀ sz rd c fl, m ≠ .fpuLoad sz rd (.const c) fl) :
    m.isLitLoad = false := by
  cases hl : m.isLitLoad with
  | false => rfl
  | true =>
    exfalso
    unfold MInst.isLitLoad at hl
    split at hl
    · exact h _ _ _ _ rfl
    · cases hl

/-- Renaming keeps the literal-pool load. -/
theorem isLitLoad_mapRegs (g : Reg → Reg) (i : MInst) :
    (i.mapRegs g).isLitLoad = i.isLitLoad := by
  cases i with
  | fpuLoad sz rd m fl => simp only [MInst.mapRegs]; cases m <;> rfl
  | _ => (try simp only [MInst.mapRegs]) <;> rfl

/-- The load of a stack-passed parameter is no literal-pool load. -/
theorem stackArgLoad_isLitLoad (r : Reg) (b : Nat) (off : Int) :
    (stackArgLoad r b (.fpOffset off)).isLitLoad = false := by
  unfold stackArgLoad
  split <;> rfl

/-- The driver's result `mov`s are no literal-pool loads. -/
theorem extraOfT_isLitLoad {ctx : Ctx} {results : List Nat} {rss : List (List Reg)} {m : MInst}
    (h : m ∈ extraOfT ctx results rss) : m.isLitLoad = false := by
  unfold extraOfT at h
  simp only [List.mem_filterMap] at h
  obtain ⟨⟨r, rs⟩, -, hq⟩ := h
  simp only at hq
  split at hq
  · cases hq
  · cases hq; rfl
  · cases hq

/-! ## `lowerFunction`'s VCode -/

/-- **`lowerFunction`'s VCode of the float scope has no literal-pool load.** -/
theorem lower_noLitTF {f : Clif.Function} {vc : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isLitLoad = false := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hs.externsE hl
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hsc : InstScopeTF ctx := (ctxSpec_of hb).instScopeTF hs.subsetTF
  have hx : CallsE f ctx := callsE_of_externs hs.externsE ctx
  have hd : Pool.DataP ctx := Pool.dataP_of_build hb
  have hnm : LowerNoMatch ctx := fun _ _ _ hi hc _ hr hroot =>
    lower_nonroot_nomatchTF_calls hctx hsc hx hi hc hr hroot
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  have hall := vcBlocksT_all' (fun m => m.isLitLoad = false)
    (fun R _ _ m h => by rw [isLitLoad_mapRegs]; exact h) (fun _ => rfl)
    (fun n c b off => stackArgLoad_isLitLoad _ b off)
    (fun _ => rfl) (f := f) (ctx := ctx) (bl := bl)
    (fun bi B L j stm sl hB hL hj hsl => by
      obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
      obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
      obtain ⟨tr, hrun⟩ := hc j sl hsl
      rw [hstart bi L hL] at hrun
      obtain ⟨ms, hms, hcov⟩ := Pool.stmt_noPool hctx hsc hnm hd hi hic hrun
      have hcov' : ∀ m ∈ ms, m.isLitLoad = false := fun m hm => isLitLoad_of_ne (hcov m hm)
      rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
      simpa using hcov')
    (fun bi B L j stm sl hB hL hj hsl m hm => extraOfT_isLitLoad hm)
    (fun bi B L hB hL => by
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      intro m hm
      rcases mem_fixTry hm with hm | ⟨c, ti, rfl⟩
      · cases ht : B.term.isTry with
        | false =>
          obtain ⟨-, hdat, out, tr, hc⟩ := hn ht
          obtain ⟨ms, hms, hcov⟩ := Pool.termCall_noPool hd hti hdat hc
          rw [hms, htst] at hm
          exact isLitLoad_of_ne (hcov m (by simpa using hm))
        | true =>
          obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
            cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
            · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
            · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
          obtain ⟨T, -, hdat, -, -, -, -, out, tr, hc⟩ := hy et het
          obtain ⟨ms, hms, hcov⟩ := Pool.tryCall_noPool hd hdat hc
          rw [hms] at hm
          exact isLitLoad_of_ne (hcov m (by simpa using hm))
      · rfl)
  rw [hvb]
  exact hall

/-! ## `prepare`'s output -/

/-- `prepare` adds no literal-pool load: its instructions are the input's, retargeted control
instructions, or edge blocks' `jump`s. -/
theorem noPoolB_of_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isLitLoad = false) :
    vcp.noPoolB = true := by
  have H := prepare_all (P := fun i => i.isLitLoad = false) h hd
    (fun _ hctl => isLitLoad_of_covered2 (.inl hctl)) hc
  unfold VCode.noPoolB
  rw [List.all_eq_true]
  intro vb hvb
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [Array.getElem?_toList] at hb hk
  rw [H b vb k i hb hk]
  rfl

/-- **The float scope's prepared VCode has no literal-pool load** (#1002): its `f64const`s are
`Compile.f64PoolFree`. -/
theorem noPoolB_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) : vcp.noPoolB = true :=
  noPoolB_of_prepare hp (Spill.prepDomain_ofTF hs hl) (lower_noLitTF hs hl)

/-- `noPoolB_lowerTF` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem noPoolB_cleanup_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) (hp : prepare (prune vc) = .ok vcp) : vcp.noPoolB = true :=
  noPoolB_of_prepare hp (prune_prepDomain (Spill.prepDomain_ofTF hs hl))
    (prune_insts (lower_noLitTF hs hl))

/-- **The literal loads' reach on the float scope** (#1002): `poolReachB` of the prepared VCode
holds for every function of the scope, whatever its size (there is no literal-pool load). -/
theorem poolReachB_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) : poolReachB vcp = true :=
  poolReachB_of_noPool (noPoolB_lowerTF hs hl hp)

/-- `poolReachB_lowerTF` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem poolReachB_cleanup_lowerTF {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) (hp : prepare (prune vc) = .ok vcp) : poolReachB vcp = true :=
  poolReachB_of_noPool (noPoolB_cleanup_lowerTF hs hl hp)

/-- **The typed scope's prepared VCode has no literal-pool load** (`noPoolB_lowerTF`). -/
theorem noPoolB_lowerT {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) : vcp.noPoolB = true :=
  noPoolB_lowerTF hs.toTF hl hp

/-- `noPoolB_lowerT` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem noPoolB_cleanup_lowerT {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : prepare (prune vc) = .ok vcp) : vcp.noPoolB = true :=
  noPoolB_cleanup_lowerTF hs.toTF hl hp

/-- **The literal loads' reach on the typed scope** (`poolReachB_lowerTF`). -/
theorem poolReachB_lowerT {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) : poolReachB vcp = true :=
  poolReachB_lowerTF hs.toTF hl hp

/-- `poolReachB_lowerT` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem poolReachB_cleanup_lowerT {f : Clif.Function} {vc vcp : VCode} (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : prepare (prune vc) = .ok vcp) : poolReachB vcp = true :=
  poolReachB_cleanup_lowerTF hs.toTF hl hp

end E2E

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## Two-way coverage -/

/-- A covered instruction that is no literal-pool load is a control form or `FormOk`. -/
theorem covered2_of_noLit {cx : FnCtx} {i : MInst}
    (h : i.isCtl = true ∨ FormOk cx i = true ∨ i.isPoolLoad = true) (hn : i.isLitLoad = false) :
    i.isCtl = true ∨ FormOk cx i = true := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form h
    exact absurd hn (by simp [MInst.isLitLoad])

/-- Three-way coverage of a VCode without literal-pool load is two-way. -/
theorem formsCovered2_of_noPool {vcp : VCode} (h : FormsCovered default vcp)
    (hn : vcp.noPoolB = true) : FormsCovered2 vcp := by
  intro b vb k i hvb hi
  simp only [VCode.noPoolB, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
  exact covered2_of_noLit (h b vb k i hvb hi)
    (hn vb (List.mem_of_getElem? (by simpa using hvb)) i (List.mem_of_getElem? (by simpa using hi)))

/-- **Two-way form coverage on the typed scope** (#1002): every instruction of `prepare`'s output
of `lowerFunction`'s VCode is a control form or `FormOk`; the scope's `f64const`s need no
literal pool, so the typed analysis's third category (`MInst.isPoolLoad`) does not occur. -/
theorem formsCovered2_completeT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) : FormsCovered2 vcp :=
  formsCovered2_of_noPool (formsCovered_completeT hdom hs hst hsel hl hp default)
    (E2E.noPoolB_lowerT hs hl hp)

end Backend.Proof.Driver
