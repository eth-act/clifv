import FV.Backend.Proof.RelocProvSound
import FV.Backend.Proof.RelocProvModel
import FV.Backend.Proof.RelocProvRoot
import FV.Backend.Proof.RelocProvEmit
import FV.Backend.Proof.LowerComplete

/-!
# Name provenance of the ISLE lowering: the driver (L1e, #216)

`lowerFunction_refs`: every instruction of `lowerFunction f`'s VCode has its references in `f`
(`RefsOk f`: a call's symbol is an external function of `f`, an address load's name and offset
are declared by `f`). The ISLE runs of the driver are covered by the abstract interpretation's
soundness (`soundAt`) with the provenance model (`provModel`, `RelocProvModel`), the table
`provTab` and the root checks `provRoot_ok`/`provRootBranch_ok` (`RelocProvTab`,
`RelocProvRoot`); the strict `emit` precondition makes every emitted instruction `RefsOk`. The
driver's own instructions (`args`, the parameter loads, result `mov`s, edge `jump`s) have no
references, vreg renaming keeps them (`refsOk_mapRegs`), and the `tryCall` of a `try_call` is the emitted `call`'s.
The assembly follows `lowerCheck_complete`'s `ElfTlsGetAddr` part (`LowerComplete`).
-/

namespace Backend.Proof.RelocProv

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- The emitted code of a run whose state invariant is `RefsSince`. -/
theorem refsSince_of {f : Clif.Function} {s s' : LState} (h : RefsSince f s s') :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m := h

set_option maxRecDepth 100000 in
/-- A statement's lowering emits only instructions with `f`'s references. -/
theorem stmt_refs {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hcl : CleanP ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program provTab true [NA.c0] NA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp provRoot_ok rl hrl
    simp only [provRootOk, Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with hcr | ha
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · exact .inl ha
  have hins : Holds2 (provModel ctx hcl s).γ s [NA.c0] [.inst ii] := ⟨γP_inst _ _ _, trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (provModel ctx hcl s) (cfg := {}) rfl provTab_ok 1000000).root
    T.lower.ret T.lower.id T.lower _ _ [NA.c0] NA.top [.inst ii] s #[] out s' tr'
    data_program.t686 term_686_kind hrules hins (refsSince_refl _ _) happ
  rw [← hctx.func]
  exact refsSince_of hIs

set_option maxRecDepth 100000 in
/-- `lower_branch` in a clean context emits only instructions with `ctx.func`'s references. -/
theorem branch_refs {ctx : Ctx} (hcl : CleanP ctx) {ti : Nat} {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk ctx.func m := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 (provModel ctx hcl s).γ s [NA.c0, NA.c0] [.inst ti, .labels targets] :=
    ⟨γP_inst _ _ _, γP_noNames (by simp [vNames]) (by simp [vInts]) (by simp [VGood]), trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (provModel ctx hcl s) (cfg := {}) rfl provTab_ok 1000000).root
    T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [NA.c0, NA.c0] NA.top _ s #[] out s' tr'
    data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp provRootBranch_ok rl hrl)) hins (refsSince_refl _ _) happ
  exact refsSince_of hIs

set_option maxRecDepth 100000 in
/-- A terminator's lowering (`lower` on `return`/`trap`, `lower_branch` on a branch) emits only
instructions with `f`'s references. -/
theorem termCall_refs {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hcl : CleanP ctx)
    {ti : Nat} (hti : ti < ctx.insts.size) {t : Clif.Terminator} {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m := by
  have hcl' := cleanP_termCtx hcl hd ti
  have hf : (termCtx ctx ti data).func = f := hctx.func
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program provTab true [NA.c0] NA.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp provRoot_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        simp only [provRootOk] at hf
        rcases hroot with h1 | h1 <;> rw [h1] at hf <;>
          exact .inl (by simpa (config := { decide := true }) using hf)
    have hins : Holds2 (provModel _ hcl' s).γ s [NA.c0] [.inst ti] := ⟨γP_inst _ _ _, trivial⟩
    obtain ⟨hIs, -⟩ := (soundAt (provModel _ hcl' s) (cfg := {}) rfl provTab_ok 1000000).root
      T.lower.ret T.lower.id T.lower _ _ [NA.c0] NA.top [.inst ti] s #[] out s' tr'
      data_program.t686 term_686_kind hrules hins (refsSince_refl _ _) happ
    rw [← hf]
    exact refsSince_of hIs
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => rw [← hf]; exact branch_refs hcl' h
  | brif c a b => rw [← hf]; exact branch_refs hcl' h
  | brTable x d tb => rw [← hf]; exact branch_refs hcl' h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

/-- A `try_call`'s lowering (`lower_branch`) emits only instructions with `f`'s references. -/
theorem tryCall_refs {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hcl : CleanP ctx)
    {ti : Nat} {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data)
    {trs : List Reg × List Reg} {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, RefsOk f m := by
  rw [← hctx.func] at hd ⊢
  exact branch_refs (cleanP_tryCtx hcl hd ti trs) h

/-- `fixTry`'s `tryCall` is the last `call` of the terminator's code. -/
theorem mem_fixTry_call {T : Option TryLow} {ms : List MInst} {m : MInst} (h : m ∈ fixTry T ms) :
    m ∈ ms ∨ ∃ c ti, m = .tryCall c ti ∧ .call c ∈ ms := by
  unfold fixTry at h
  split at h
  · unfold tryFix at h
    split at h
    · rename_i c hl
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl (List.dropLast_subset _ h)
      · exact .inr ⟨_, _, rfl, List.mem_of_getLast? hl⟩
    · exact .inl h
  · exact .inl h

/-- **Name provenance of the lowering**: every instruction of `lowerFunction f`'s VCode has its
references in `f`. -/
theorem lowerFunction_refs {f : Clif.Function} {vc : VCode} (hs : LowerScope f)
    (h : lowerFunction f = .ok vc) : AllInsts (RefsOk f) vc := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, -⟩ := lowerFunction_run h
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcl : CleanP ctx := cleanP_of_build hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  have hemp := lowBlocks_emptied hl
  have hall := vcBlocks_all (RefsOk f) (fun R _ _ m hm => (refsOk_mapRegs R m).mpr hm)
    (fun _ => trivial) (fun _ _ _ => trivial) (fun _ => trivial) (f := f) (bl := bl)
    (fun bi B L j stm sl hB hL hj hsl => by
      obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
      obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
      obtain ⟨tr, hrun⟩ := hc j sl hsl
      rw [hstart bi L hL] at hrun
      obtain ⟨ms, hms, hok⟩ := stmt_refs hctx hcl hi hic hrun
      rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
      exact all_extraOf (fun _ _ _ => trivial) (by simpa using hok) _ _)
    (fun bi B L hB hL => by
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hti : L.start + B.body.length < ctx.insts.size := by
        have := hcf.term bi B hB
        rw [← hstart bi L hL] at this
        exact (Array.getElem?_eq_some_iff.mp this).1
      have hterms : ∀ m ∈ L.tst'.emitted.toList, RefsOk f m := by
        cases ht : B.term.isTry with
        | false =>
          obtain ⟨-, hd, out, tr, hc⟩ := hn ht
          obtain ⟨ms, hms, hok⟩ := termCall_refs hctx hcl hti hd hc
          rw [hms, htst]
          simpa using hok
        | true =>
          obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
            cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
            · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
            · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
          obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
          obtain ⟨ms, hms, hok⟩ := tryCall_refs hctx hcl hd hc
          rw [hms]
          simpa using hok
      intro m hm
      rcases mem_fixTry_call hm with hm | ⟨c, ti, rfl, hc⟩
      · exact hterms m hm
      · exact fun n hn => hterms _ hc n hn)
  intro vb hvb' m hm
  rw [hvb] at hvb'
  exact hall vb hvb' m hm

end Backend.Proof.RelocProv
