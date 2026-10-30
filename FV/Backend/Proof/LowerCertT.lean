import FV.Backend.Proof.LowerCert
import FV.Backend.Proof.IselFlowT
import FV.Backend.Proof.IselExclTF
import FV.Backend.Proof.LowerLoopCtxTF

/-!
# Completeness of `lowerCheckT`: the SSA availability certificate, typed scope

`LowerCert` over the typed scope (`LowerScopeT`): on `Dominated` input the aliases
`lowerFunction` records are well founded (`alias_factsT`: an alias target is a fresh vreg of
the statement or a value its instruction reaches through its operands, now by the typed flow
analysis `stmt_flowT`), and the certificate conditions hold (`certOk_completeT`). The proofs
are `LowerCert`'s; only the flow fact of an alias changes (`alias_srcT`). The section's lemmas
hold over the float scope `LowerScopeTF` (`alias_factsTF`, `certOk_completeTF`; the typed scope
gives it, `LowerScopeT.toTF`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

variable {f : Clif.Function}

/-- The externs of a typed-scope function have integer signatures. -/
theorem externsE_of (h : Compile.functionET f = true) : f.externs.all (Compile.sigE ·.2.sig) = true := by
  simp only [Compile.functionET, Bool.and_eq_true] at h
  exact h.1.1.1.2

section
variable {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow}
  (hd : Dominated f) (hsc : LowerScopeTF f) (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
include hd hsc hb hl

omit hd in
/-- An alias `(r, o)`: `r` is a result of a statement whose lowering returned `vreg o`, a fresh
vreg of that call or a value its instruction reaches (`stmt_flowT`). -/
theorem alias_srcT {r o : Nat} (h : (r, o) ∈ aliasOf f bl) :
    ∃ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ B.body[j]? = some stm ∧ L.sl[j]? = some sl ∧
      r ∈ stm.results ∧
      ((sl.st.nextVreg ≤ o ∧ o < sl.st'.nextVreg) ∨ Prov ctx (blockStart f bi + j) o) := by
  obtain ⟨bi, B, L, j, stm, sl, hB, hL, hs, hsl, hr, rs, c, hrs, hrs'⟩ := mem_aliasOf h
  have hF := ctxFacts_of hb
  obtain ⟨-, hbl⟩ := lowBlocks_spec hl
  obtain ⟨-, hcall, -⟩ := hbl bi B L hB hL
  obtain ⟨tr, hrun⟩ := hcall j sl hsl
  rw [(lowBlocks_start hl).2 bi L hL] at hrun
  obtain ⟨info, hi, hc, hres⟩ := hF.stmt bi B j stm hB hs
  have hctx := ctxInvT_ofF hsc hb
  have hnm : LowerNoMatch ctx := fun _ _ _ hi hc _ hr hroot =>
    lower_nonroot_nomatchTF_calls hctx ((ctxSpec_of hb).instScopeTF hsc.subsetTF)
      (callsE_of_externs hsc.externsE ctx) hi hc hr hroot
  exact ⟨bi, B, L, j, stm, sl, hB, hL, hs, hsl, hr,
    stmt_flowG hctx hnm hF.tryRegs hi hc hrun sl.rss rfl
    (by rw [hres]; exact List.ne_nil_of_mem hr) rs hrs o c hrs'⟩

/-- `alias_factsT` under the section's hypotheses: unique keys below the first temporary, well
founded (rank: the number of values `Prov` reaches from the key's definition). -/
theorem alias_factsT' :
    ((aliasOf f bl).map (·.1)).Nodup ∧ (∀ p ∈ aliasOf f bl, p.1 < st0.nextVreg) ∧
      AliasWF (aliasOf f bl) := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hkeys := aliasOf_keys f bl
  have hk : ∀ p ∈ aliasOf f bl, p.1 < st0.nextVreg := fun p hp =>
    lt_of_valueDefs hF (hkeys.subset (List.mem_map_of_mem hp))
  refine ⟨hssa.sublist hkeys, hk, ?_⟩
  classical
  refine ⟨fun x => (List.range st0.nextVreg).countP fun y =>
    decide (∃ d, ctx.defInst? x = some d ∧ Prov ctx d y), ?_⟩
  intro p hp q hq hqp
  obtain ⟨x, o⟩ := p
  obtain ⟨o', o''⟩ := q
  simp only at hqp ⊢
  subst hqp
  obtain ⟨bi, B, L, j, stm, sl, hB, hL, hs, hsl, hx, hfl⟩ := alias_srcT hsc hb hl hp
  have ho : o' < st0.nextVreg := hk _ hq
  have hprov : Prov ctx (blockStart f bi + j) o' := by
    rcases hfl with ⟨h1, -⟩ | h
    · have := (((driver_ord hl).1 bi L hL).stmt j sl hsl).1; omega
    · exact h
  obtain ⟨bi2, B2, L2, j2, stm2, sl2, hB2, -, hs2, -, ho2, -⟩ := alias_srcT hsc hb hl hq
  have hdx := defInst_res hF hssa hB hs hx
  have hdo := defInst_res hF hssa hB2 hs2 ho2
  apply certCountP_lt (a := o')
  · intro y _ h
    simp only [decide_eq_true_eq] at h ⊢
    obtain ⟨d, hd1, hd2⟩ := h
    rw [hdo] at hd1; cases hd1
    exact ⟨_, hdx, prov_trans hprov hdo hd2⟩
  · exact List.mem_range.mpr ho
  · simp only [decide_eq_true_eq]; exact ⟨_, hdx, hprov⟩
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro d hd1 hd2
    rw [hdo] at hd1; cases hd1
    have := prov_avail hd hb hB2 hs2 hd2
    exact ((mem_av hB2).mp this).2 ⟨j2, stm2, Nat.le_refl _, hs2, ho2⟩

/-- Following aliases from a value satisfying an invariant closed under `Prov` of definitions:
the end satisfies it, or is a fresh vreg of the statement defining a value satisfying it. -/
theorem path_invT (I : Nat → Prop)
    (hI : ∀ r d y, I r → ctx.defInst? r = some d → Prov ctx d y → I y)
    {x z : Nat} (hp : AliasPath (aliasOf f bl) x z) (hx : I x) :
    I z ∨ ∃ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow) (r : Nat),
      f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ B.body[j]? = some stm ∧ L.sl[j]? = some sl ∧
      r ∈ stm.results ∧ I r ∧ sl.st.nextVreg ≤ z ∧ z < sl.st'.nextVreg := by
  have hF := ctxFacts_of hb
  have hk := (alias_factsT' hd hsc hb hl).2.1
  induction hp with
  | refl => exact .inl hx
  | step hxy hyz ih =>
    obtain ⟨bi, B, L, j, stm, sl, hB, hL, hs, hsl, hr, hfl⟩ := alias_srcT hsc hb hl hxy
    rcases hfl with ⟨h1, h2⟩ | h
    · have hst := (((driver_ord hl).1 bi L hL).stmt j sl hsl).1
      rw [path_nonkey (fun q hq e => by have := hk q hq; omega) hyz]
      exact .inr ⟨bi, B, L, j, stm, sl, _, hB, hL, hs, hsl, hr, hx, h1, h2⟩
    · exact ih (hI _ _ _ hx (defInst_res hF hd.ssa hB hs hr) h)

/-- An entry value not redefined in the block is not renamed onto one of its parameters. -/
theorem gn_not_parT {tl x : Nat} (hx : x ∈ (availIn f ctx).getD tl []) (hxd : x ∉ defsOf f tl) :
    gnOf f st0 bl x ∉ parsOf f tl := by
  obtain ⟨hu, hk, hwf⟩ := alias_factsT' hd hsc hb hl
  rcases path_invT hd hsc hb hl (fun z => z ∈ (availIn f ctx).getD tl [] ∧ z ∉ defsOf f tl)
      (fun r d y hr hd' hp => prov_entry hd hb hr.1 hr.2 hd' hp)
      (show AliasPath (aliasOf f bl) x (gnOf f st0 bl x) from (gn_path hu hk hwf x).1)
      ⟨hx, hxd⟩ with
    h | ⟨bi, B, L, j, stm, sl, r, hB, hL, hs, hsl, -, -, h1, -⟩
  · exact ((inFix_fixOk (gn := id)).cand tl _ h.1).2.2.2.2.1
  · intro hp
    have := pars_lt' (ctxFacts_of hb) hp
    have := (((driver_ord hl).1 bi L hL).stmt j sl hsl).1
    omega

/-- **V1b**: an entry value of `availIn` not redefined in the block is one of `inFix` with the
validator's renaming. -/
theorem avail_sub_inT {tl x : Nat} (hx : x ∈ (availIn f ctx).getD tl []) (hxd : x ∉ defsOf f tl) :
    x ∈ (inFix f ctx (gnOf f st0 bl)).getD tl [] := by
  have hG := inFix_fixOk (f := f) (ctx := ctx) (gn := id)
  let D : Nat → Nat → Prop := fun tl x =>
    x ∈ (availIn f ctx).getD tl [] ∧ (x ∉ defsOf f tl ∨ gnOf f st0 bl x ∉ parsOf f tl)
  have hD : FixOk f ctx (gnOf f st0 bl) D := by
    refine ⟨fun tl x ⟨h, h'⟩ => ?_, fun tl x ⟨h, _⟩ p hp => ?_, fun tl x ⟨h, _⟩ y hy => ?_⟩
    · obtain ⟨a, b, c, d, e, -⟩ := hG.cand tl x h
      refine ⟨a, b, c, d, e, ?_⟩
      rcases h' with h' | h'
      · exact gn_not_parT hd hsc hb hl h h'
      · exact h'
    · rcases hG.out tl x h p hp with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · by_cases hxd : x ∈ defsOf f p
        · exact .inr (.inl hxd)
        · exact .inr (.inr ⟨h, .inl hxd⟩)
    · obtain ⟨h1, h2⟩ := hG.clo tl x h y hy
      exact ⟨h1.imp_right fun h => ⟨h, .inl h2⟩, h2⟩
  exact inFix_greatest hD ⟨hx, .inl hxd⟩

/-- **V1b**: the available values of `inFix` with the validator's renaming are those of
`availIn`. -/
theorem avail_eqT {bi j x : Nat} :
    x ∈ availOf f (inFix f ctx (gnOf f st0 bl)) bi j ↔ x ∈ availOf f (availIn f ctx) bi j := by
  cases hB : f.blocks[bi]? with
  | none => simp [availOf, hB]
  | some B =>
    rw [mem_av hB, mem_av hB]
    by_cases hxd : x ∈ defsOf f bi
    · obtain ⟨B', k, s, hB', hs, hk⟩ := mem_defsOf.mp hxd
      rw [hB] at hB'; cases hB'
      have e : ∀ P Q : Prop, ((P ∨ Q ∨ ∃ (k : Nat) (s : Clif.Stmt), k < j ∧ B.body[k]? = some s ∧
          x ∈ s.results) ∧ ¬ ∃ (k : Nat) (s : Clif.Stmt), j ≤ k ∧ B.body[k]? = some s ∧
          x ∈ s.results) ↔ k < j := by
        intro P Q
        constructor
        · rintro ⟨-, h2⟩
          apply Nat.lt_of_not_le; intro hle; exact h2 ⟨k, s, hle, hs, hk⟩
        · intro hkj
          refine ⟨.inr (.inr ⟨k, s, hkj, hs, hk⟩), ?_⟩
          rintro ⟨k', s', hk', hs', hk''⟩
          have := (res_unique hd.ssa hB hs' hk'' hB hs hk).2
          omega
      rw [e, e]
    · have e : x ∈ (inFix f ctx (gnOf f st0 bl)).getD bi [] ↔ x ∈ (availIn f ctx).getD bi [] :=
        ⟨inFix_sub _, fun h => avail_sub_inT hd hsc hb hl h hxd⟩
      rw [e]

/-- **The clobber condition**: the resolved vreg of a value of block `bi` is a value of `f`, or
a fresh vreg of a statement of another block or of an earlier statement of `bi` (before the
value is available). -/
theorem gn_freshT {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) {x : Nat}
    (hx : x ∈ (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).ent ++ B.body.flatMap (·.results)) :
    gnOf f st0 bl x < st0.nextVreg ∨ ∃ (bi' : Nat) (L' : BLow) (j' : Nat) (sl' : SLow),
      bl[bi']? = some L' ∧ L'.sl[j']? = some sl' ∧ sl'.st.nextVreg ≤ gnOf f st0 bl x ∧
      gnOf f st0 bl x < sl'.st'.nextVreg ∧
      (bi' = bi → j' < (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).first ctx x) := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hD := defsAt_of hd hb hl hB hL
  obtain ⟨hu, hk, hwf⟩ := alias_factsT' hd hsc hb hl
  have hpath : AliasPath (aliasOf f bl) x (gnOf f st0 bl x) := (gn_path hu hk hwf x).1
  have hGv : ∀ tl x, x ∈ (availIn f ctx).getD tl [] → x ∈ valueDefs f :=
    fun tl x h => ((inFix_fixOk (gn := id)).cand tl x h).2.2.2.1
  by_cases hxd : x ∈ B.body.flatMap (·.results)
  · obtain ⟨k, stm, hs, hxk⟩ := mem_defs.mp hxd
    have hfirst : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).first ctx x = k + 1 := by
      simp only [Avail.first, (dpos_iff hD).mpr ⟨stm, hs, hxk⟩]
    rw [hfirst]
    have hdx := defInst_res hF hssa hB hs hxk
    rcases path_invT hd hsc hb hl (fun r => r = x ∨ r ∈ availOf f (availIn f ctx) bi k)
        (fun r d y hr hd' hp => by
          rcases hr with rfl | hr
          · rw [hdx] at hd'; cases hd'
            exact .inr (prov_avail hd hb hB hs hp)
          · exact .inr (prov_closed hd hb hr hd' hp)) hpath (.inl rfl) with
      h | ⟨bi', B', L', j', stm', sl', r, hB', hL', hs', hsl', hr, hI, h1, h2⟩
    · left
      rcases h with h | h
      · rw [h]; exact lt_of_valueDefs hF (mem_valueDefs_res hB hs hxk)
      · exact lt_of_valueDefs hF (avail_vals hGv h)
    · refine .inr ⟨bi', L', j', sl', hL', hsl', h1, h2, fun e => ?_⟩
      subst e
      rcases hI with rfl | hI
      · have := (res_unique hssa hB hs hxk hB' hs' hr).2; omega
      · rw [hB] at hB'; cases hB'
        have := ((mem_av hB).mp hI).2
        apply Nat.lt_succ_of_lt
        apply Nat.lt_of_not_le; intro hle; exact this ⟨j', stm', hle, hs', hr⟩
  · have hfirst : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).first ctx x = 0 := by
      unfold Avail.first
      cases h : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).dpos ctx x with
      | none => rfl
      | some k =>
        obtain ⟨stm, hs, hx'⟩ := (dpos_iff hD).mp h
        exact absurd (mem_defs.mpr ⟨k, stm, hs, hx'⟩) hxd
    rw [hfirst]
    have hxe : x ∈ B.params.map (·.1) ∨ x ∈ (inFix f ctx (gnOf f st0 bl)).getD bi [] := by
      rw [List.mem_append, Avail.of_ent, List.mem_append] at hx
      rcases hx with h | h
      · exact h
      · exact absurd h hxd
    rcases hxe with hxp | hxi
    · left
      have hnk : ∀ q ∈ aliasOf f bl, q.1 ≠ x := by
        intro q hq e
        obtain ⟨bi', B', L', j', stm', sl', hB', -, hs', -, hr, -⟩ := alias_srcT hsc hb hl
          (show (q.1, q.2) ∈ aliasOf f bl from hq)
        rw [e] at hr
        exact par_not_res hssa hB hxp hB' hs' hr
      rw [path_nonkey hnk hpath]
      exact lt_of_valueDefs hF (mem_valueDefs_par hB hxp)
    · have hxG := inFix_sub _ hxi
      have hxd' : x ∉ defsOf f bi := by rw [defsOf_of hB]; exact hxd
      rcases path_invT hd hsc hb hl (fun z => z ∈ (availIn f ctx).getD bi [] ∧ z ∉ defsOf f bi)
          (fun r d y hr hd' hp => prov_entry hd hb hr.1 hr.2 hd' hp) hpath ⟨hxG, hxd'⟩ with
        h | ⟨bi', B', L', j', stm', sl', r, hB', hL', hs', hsl', hr, hI, h1, h2⟩
      · exact .inl (lt_of_valueDefs hF (hGv _ _ h.1))
      · refine .inr ⟨bi', L', j', sl', hL', hsl', h1, h2, fun e => ?_⟩
        subst e
        exact absurd (mem_defsOf.mpr ⟨B', j', stm', hB', hs', hr⟩) hI.2

/-- Every block passes `certBlockOk`. -/
theorem certBlock_okT {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) :
    certBlockOk f ctx st0 (gnOf f st0 bl) f.blocks.toArray bl.toArray
      (inFix f ctx (gnOf f st0 bl)) bi B L = true := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hD := defsAt_of hd hb hl hB hL
  have hlen' := (lowBlocks_start hl).1
  have hord := (driver_ord hl).1 bi L hL
  have hpair := (driver_ord hl).2
  have hIn := inFix_fixOk (f := f) (ctx := ctx) (gn := gnOf f st0 bl)
  have huse := hd.uses ctx ranges st0 hb bi B hB
  refine certBlockOk_of ((lowBlocks_spec hl).2 bi B L hB hL).1 hD (fun k stm hs => ?_)
    (fun k sl hsl => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun b hbE => ?_)
  · exact ⟨stmt_nodup hssa hB hs, fun y hy =>
      (mem_avail hB hD).mp ((avail_eqT hd hsc hb hl).mpr (huse.1 k stm hs y hy))⟩
  · obtain ⟨-, h2, -, h4⟩ := hord.stmt k sl hsl
    exact ⟨h2, fun sl' h' => h4 (k + 1) sl' (Nat.lt_succ_self k) h'⟩
  · refine ⟨?_, ?_, ?_⟩
    · -- a value of `f`
      apply lt_of_valueDefs hF
      rw [List.mem_append, Avail.of_ent, List.mem_append] at hx
      rcases hx with (h | h) | h
      · exact mem_valueDefs_par hB h
      · exact (hIn.cand bi x h).2.2.2.1
      · obtain ⟨k, stm, hs, hk⟩ := mem_defs.mp h
        exact mem_valueDefs_res hB hs hk
    · -- closure
      by_cases hxd : x ∈ B.body.flatMap (·.results)
      · obtain ⟨k, stm, hs, hxk⟩ := mem_defs.mp hxd
        have hfirst : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).first ctx x = k + 1 := by
          simp only [Avail.first, (dpos_iff hD).mpr ⟨stm, hs, hxk⟩]
        rw [hfirst]
        intro y hy
        rw [defArgs_res hF hssa hB hs hxk] at hy
        have := (mem_iff_first hD).mp
          ((mem_avail hB hD).mp ((avail_eqT hd hsc hb hl).mpr (huse.1 k stm hs y hy)))
        exact ⟨this.1, by omega⟩
      · have hfirst : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).first ctx x = 0 := by
          unfold Avail.first
          cases h : (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi).dpos ctx x with
          | none => rfl
          | some k =>
            obtain ⟨stm, hs, hx'⟩ := (dpos_iff hD).mp h
            exact absurd (mem_defs.mpr ⟨k, stm, hs, hx'⟩) hxd
        rw [hfirst]
        rw [List.mem_append, Avail.of_ent, List.mem_append] at hx
        rcases hx with (hxp | hxi) | h
        · intro y hy
          simp [defArgs, defInst_par hF hssa hB hxp] at hy
        · intro y hy
          obtain ⟨h1, h2⟩ := hIn.clo bi x hxi y hy
          have : y ∈ availOf f (inFix f ctx (gnOf f st0 bl)) bi 0 := by
            refine (mem_av hB).mpr ⟨?_, fun ⟨k, s, _, hs, hk⟩ =>
              h2 (mem_defsOf.mpr ⟨B, k, s, hB, hs, hk⟩)⟩
            rcases h1 with h | h
            · exact .inl (by rwa [parsOf_of hB] at h)
            · exact .inr (.inl h)
          exact (mem_iff_first hD).mp ((mem_avail hB hD).mp this)
        · exact absurd h hxd
    · -- clobber
      rcases gn_freshT hd hsc hb hl hB hL hx with hlt | ⟨bi', L', j', sl', hL', hsl', h1, h2, h3⟩
      · refine ⟨fun sl last hsl _ => .inl ?_, fun ⟨h, _⟩ => ?_⟩
        · have := (hord.stmt _ sl hsl).1; omega
        · have := hord.term.1; omega
      · rcases Nat.lt_trichotomy bi' bi with hlt | rfl | hgt
        · have ho := hpair bi' bi L' L hlt hL' hL
          have hs' := ((driver_ord hl).1 bi' L' hL').stmt j' sl' hsl'
          have ht' := ((driver_ord hl).1 bi' L' hL').term
          refine ⟨fun sl last hsl _ => .inl ?_, fun ⟨h, _⟩ => ?_⟩
          · have := (ho.stmt _ sl hsl).1; omega
          · have := ho.term.1; omega
        · rw [hL] at hL'; cases hL'
          have hj := h3 rfl
          have hs' := hord.stmt j' sl' hsl'
          refine ⟨fun sl last hsl _ => .inl ?_, fun ⟨h, _⟩ => ?_⟩
          · have := hs'.2.2.2 _ sl hj hsl; omega
          · have := hs'.2.2.1; omega
        · have ho := hpair bi bi' L L' hgt hL hL'
          have hs' := (ho.stmt j' sl' hsl').1
          refine ⟨fun sl last _ hlast => .inr ?_, fun ⟨_, h⟩ => ?_⟩
          · have := (hord.stmt _ last hlast).2.2.1; have := hord.term.2; omega
          · omega
  · exact (mem_avail hB hD).mp ((avail_eqT hd hsc hb hl).mpr (huse.2 y hy))
  · refine ⟨hsc.noEntryPred B (List.mem_of_getElem? hB) b (edge_succ hbE),
      edgeOk_of hlen' (fun tl TB TL htl hTB hTL => ?_)⟩
    have hDT := defsAt_of hd hb hl hTB hTL
    refine ⟨(List.nodup_append.mp (block_nodup hssa hTB)).1, fun x _ hm => ?_⟩
    have hxa := (mem_avail hTB hDT).mpr hm
    obtain ⟨hm1, hm2⟩ := (mem_av hTB).mp hxa
    have hxd : x ∉ defsOf f tl := fun h => by
      obtain ⟨T, k, s, hT, hs, hk⟩ := mem_defsOf.mp h
      rw [hTB] at hT; cases hT
      exact hm2 ⟨k, s, Nat.zero_le _, hs, hk⟩
    by_cases hxp : x ∈ TB.params.map (·.1)
    · exact ⟨.inl hxp, .inl ⟨hxp, defInst_par hF hssa hTB hxp⟩⟩
    · have hxi : x ∈ (inFix f ctx (gnOf f st0 bl)).getD tl [] := by
        rcases hm1 with h | h | ⟨k, _, hk, _⟩
        · exact absurd h hxp
        · exact h
        · omega
      have hxG := inFix_sub _ hxi
      refine ⟨.inr fun y hy => ?_, .inr ⟨hxp, ?_, ?_⟩⟩
      · rw [← parsOf_of hTB]; exact hd.paramFree ctx ranges st0 hb tl x hxG hxd y hy
      · have hsucc : tl ∈ succIdx f bi := by
          simp only [succIdx, hB]
          exact List.mem_filterMap.mpr ⟨b, edge_succ hbE, htl⟩
        have hout := hIn.out tl x hxi bi hsucc
        refine (mem_avail hB hD).mp ((mem_av hB).mpr ⟨?_, ?_⟩)
        · rcases hout with h | h | h
          · exact .inl (by rwa [parsOf_of hB] at h)
          · obtain ⟨B', k, s, hB', hs, hk⟩ := mem_defsOf.mp h
            rw [hB] at hB'; cases hB'
            exact .inr (.inr ⟨k, s, lt_of_getElem? hs, hs, hk⟩)
          · exact .inr (.inl h)
        · rintro ⟨k, s, hk, hs, _⟩
          have := lt_of_getElem? hs; omega
      · have := (hIn.cand tl x hxi).2.2.2.2.2
        rwa [parsOf_of hTB] at this

end

/-- **The recorded aliases of a float-scope lowering** have unique keys, below the first
temporary, and are well founded (`alias_facts` over `LowerScopeTF`). -/
theorem alias_factsTF (hd : Dominated f) (hs : LowerScopeTF f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) :
    ((aliasOf f bl).map (·.1)).Nodup ∧ (∀ p ∈ aliasOf f bl, p.1 < st0.nextVreg) ∧
      AliasWF (aliasOf f bl) :=
  alias_factsT' hd hs hb hl

/-- **The recorded aliases of a typed-scope lowering** have unique keys, below the first
temporary, and are well founded (`alias_facts` over `LowerScopeT`). -/
theorem alias_factsT (hd : Dominated f) (hs : LowerScopeT f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) :
    ((aliasOf f bl).map (·.1)).Nodup ∧ (∀ p ∈ aliasOf f bl, p.1 < st0.nextVreg) ∧
      AliasWF (aliasOf f bl) :=
  alias_factsT' hd hs.toTF hb hl

/-- **The certificate part of `lowerCheckTCF`** (float scope). -/
theorem certOk_completeTF (hd : Dominated f) (hs : LowerScopeTF f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) :
    certOk f ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl
      (inFix f ctx (gnAt (gnTable st0.nextVreg (aliasOf f bl)))) = true := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hlen := (lowBlocks_start hl).1
  have hIn := inFix_fixOk (f := f) (ctx := ctx) (gn := gnOf f st0 bl)
  simp only [certOk, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [List.getElem?_toArray]
    cases hB0 : f.blocks[0]? with
    | none => rfl
    | some B =>
      obtain ⟨L, hL0⟩ : ∃ L, bl[0]? = some L :=
        ⟨_, List.getElem?_eq_getElem (by have := lt_of_getElem? hB0; omega)⟩
      have h0 : (inFix f ctx (gnOf f st0 bl)).getD 0 [] = [] :=
        List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
          have := (hIn.cand 0 x hx).1; omega
      simp only [hL0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true']
      refine ⟨(List.nodup_append.mp (block_nodup hssa hB0)).1, fun x hx => .inr ?_⟩
      rw [Avail.of_ent, h0, List.append_nil] at hx
      exact ⟨hx, defInst_par hF hssa hB0 hx⟩
  · simp only [List.all_eq_true, List.mem_range, List.size_toArray, List.getElem?_toArray]
    intro bi hbi
    obtain ⟨B, hB⟩ : ∃ B, f.blocks[bi]? = some B := ⟨_, List.getElem?_eq_getElem hbi⟩
    obtain ⟨L, hL⟩ : ∃ L, bl[bi]? = some L := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [hB, hL]
    exact certBlock_okT hd hs hb hl hB hL
  · simp only [List.all_eq_true, List.mem_range]
    intro ii _
    split
    · rename_i info hi
      rw [List.all_eq_true]
      intro m _
      split
      · rename_i r t hr ht
        simp only [decide_eq_true_eq]
        exact (hF.types hssa).1 ii info hi m r t hr ht
      · rfl
    · rfl
  · simp only [List.all_eq_true, decide_eq_true_eq]
    exact (hF.types hssa).2

end Backend.Proof.Driver

namespace Backend.Proof.Driver

/-- **The certificate part of `lowerCheckT`** (typed scope). -/
theorem certOk_completeT {f : Clif.Function} (hd : Dominated f) (hs : LowerScopeT f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) :
    certOk f ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl
      (inFix f ctx (gnAt (gnTable st0.nextVreg (aliasOf f bl)))) = true :=
  certOk_completeTF hd hs.toTF hb hl

end Backend.Proof.Driver
