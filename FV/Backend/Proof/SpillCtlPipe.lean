import FV.Backend.Proof.SpillCtlForms
import FV.Backend.Proof.LowerCertBase

/-!
# `CtlSpillHyp` on the pipeline's output (V4 (a), step 3)

`ctlSpillHyp_of`: for `Dominated`/`LowerScope` input whose signatures pass the ABI check of
the end-to-end subset (`AbiSigsOk`: the fields `abiSigs`, `indSigs` of `E2E.InSubset`; at most
one `sret` parameter, without which two `sret` parameters are both fixed to x8 and no
allocation exists), every control form of `lowerFunction f` meets `SpillInstOk`, given
`IselCtlHyp`: the control forms the driver's ISLE runs emit have the shapes `CtlShape`.

Proven here, for the driver's part: the entry block's `Args` (its parameters in distinct
argument registers: `locsOf_regs`, at most one `sret`; distinct vregs: SSA; not renamed: a
parameter is no alias key, `param_not_result`), the `tryCall` replacing a `try_call` rule's
last call (`try_call`'s signature is `system_v`, so `clobberAll = false`: the
`clobberAll`/register-callee case, which would leave no int scratch register, is unreachable),
the edge blocks' `jump`s, and the alias renaming (it renames only values' vregs, below every
fresh def).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The ABI condition -/

/-- **The signature condition** of the end-to-end subset (`E2E.InSubset.abiSigs` and
`E2E.InSubset.indSigs`). -/
def AbiSigsOk (f : Clif.Function) : Prop :=
  (sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true) ∧
    ∀ s ∈ indSigs f, s.params.length ≤ 8 ∧ sigAbiOk s = true

theorem sret_le_of_sigAbiOk {s : Clif.Signature} (h : sigAbiOk s = true) :
    (s.params.filter (·.purpose == .sret)).length ≤ 1 := by
  unfold sigAbiOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-! ## Argument locations -/

/-- The registers of argument locations. -/
def locRegs (ls : List ArgLoc) : List Reg := ls.filterMap fun
  | .reg r => some r
  | .stack _ => none

theorem locRegs_append (a b : List ArgLoc) : locRegs (a ++ b) = locRegs a ++ locRegs b :=
  List.filterMap_append

theorem argStep_regs : ∀ (bytes : List Nat) (q : Array ArgLoc × Nat × Nat),
    locRegs q.1.toList = (List.range q.2.1).map Reg.x → q.2.1 ≤ 8 →
    ∃ k, k ≤ 8 ∧ locRegs (bytes.foldl Driver.argStep q).1.toList = (List.range k).map Reg.x
  | [], q, h, hk => ⟨q.2.1, hk, h⟩
  | b :: bytes, q, h, hk => by
    rw [List.foldl_cons]
    apply argStep_regs bytes
    · unfold Driver.argStep
      split
      · rw [Array.toList_push, locRegs_append, h]; simp [locRegs, List.range_succ]
      · rw [Array.toList_push, locRegs_append, h]; simp [locRegs]
    · unfold Driver.argStep; split <;> simp <;> omega

theorem xs_nodup (k : Nat) : ((List.range k).map Reg.x).Nodup :=
  List.Pairwise.map (S := (· ≠ ·)) Reg.x (fun _ _ h e => h (by cases e; rfl)) List.nodup_range

theorem argLocs_regs (bytes : List Nat) :
    ∃ k, k ≤ 8 ∧ locRegs (argLocs bytes).1 = (List.range k).map Reg.x := by
  rw [Driver.argLocs_eq]
  exact argStep_regs bytes (#[], 0, 0) rfl (by decide)

theorem sretFold_count (r : Reg) : ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
    (locRegs (ps.foldl sretLocStep q).1.toList).count r ≤
      (locRegs q.1.toList).count r + (locRegs q.2).count r +
        (if r = .x 8 then (ps.filter (·.purpose == .sret)).length else 0)
  | [], q => by simp
  | p :: ps, ⟨acc, rest⟩ => by
    rw [List.foldl_cons]
    refine Nat.le_trans (sretFold_count r ps (sretLocStep (acc, rest) p)) ?_
    by_cases hp : (p.purpose == .sret) = true
    · have e : sretLocStep (acc, rest) p = (acc.push (.reg (.x 8)), rest) := by
        simp [sretLocStep, hp]
      have e2 : ((p :: ps).filter (·.purpose == .sret)).length =
          (ps.filter (·.purpose == .sret)).length + 1 := by
        simp [List.filter_cons, hp]
      rw [e, e2]
      simp only [Array.toList_push, locRegs_append]
      have e3 : locRegs [ArgLoc.reg (.x 8)] = [.x 8] := rfl
      rw [e3, List.count_append]
      by_cases hr : r = .x 8
      · subst hr; simp; omega
      · simp only [hr, if_false]
        have : [Reg.x 8].count r = 0 := List.count_eq_zero.mpr (by simpa [eq_comm] using hr)
        omega
    · have e2 : ((p :: ps).filter (·.purpose == .sret)) = ps.filter (·.purpose == .sret) := by
        simp [List.filter_cons, hp]
      rw [e2]
      cases rest with
      | nil =>
        have e : sretLocStep (acc, []) p = (acc, []) := by simp [sretLocStep, hp]
        rw [e]; exact Nat.le_refl _
      | cons l rest' =>
        have e : sretLocStep (acc, l :: rest') p = (acc.push l, rest') := by simp [sretLocStep, hp]
        rw [e]
        simp only [Array.toList_push, locRegs_append]
        have e4 : locRegs (l :: rest') = locRegs [l] ++ locRegs rest' := locRegs_append [l] rest'
        rw [e4, List.count_append, List.count_append]
        omega

theorem count_le_one_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → ∀ a, l.count a ≤ 1
  | [], _, a => by simp
  | b :: l, h, a => by
    rw [List.nodup_cons] at h
    rw [List.count_cons]
    have ih := count_le_one_of_nodup h.2 a
    by_cases hab : b = a
    · subst hab
      have : l.count b = 0 := List.count_eq_zero.mpr h.1
      simp [this]
    · simp [hab]; omega

theorem nodup_of_count_le_one {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, (∀ a, l.count a ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | b :: l, h => by
    rw [List.nodup_cons]
    refine ⟨fun hb => ?_, nodup_of_count_le_one fun a => ?_⟩
    · have h1 := h b
      have h2 := List.count_pos_iff.mpr hb
      rw [List.count_cons] at h1
      simp at h1; omega
    · have := h a; rw [List.count_cons] at this; omega

theorem sigArgLocs_cases {s : Clif.Signature} {locs : List ArgLoc} {n : Nat}
    (h : sigArgLocs s = .ok (locs, n)) : ∃ bytes, locs = (argLocs bytes).1 ∨
      locs = (s.params.foldl sretLocStep (#[], (argLocs bytes).1)).1.toList := by
  unfold sigArgLocs at h
  cases hb : sigArgs s with
  | error e => rw [hb] at h; cases h
  | ok bytes =>
    simp only [hb, bind, Except.bind] at h
    split at h
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨_, .inr rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨_, .inl rfl⟩

/-- **The argument registers of a signature with at most one `sret` parameter** are distinct
registers among x0..x8. -/
theorem locsOf_regs {s : Clif.Signature} (h1 : (s.params.filter (·.purpose == .sret)).length ≤ 1) :
    (locRegs (locsOf s)).Nodup ∧ ∀ r ∈ locRegs (locsOf s), ArgReg r := by
  have xsArg : ∀ k, k ≤ 8 → ∀ r ∈ (List.range k).map Reg.x, ArgReg r := by
    intro k hk r hr
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact ⟨j, by omega, rfl⟩
  unfold locsOf
  cases hs : sigArgLocs s with
  | error e => simp [locRegs]
  | ok r =>
    obtain ⟨locs, n⟩ := r
    simp only
    obtain ⟨bytes, hl | hl⟩ := sigArgLocs_cases hs <;> subst hl
    · obtain ⟨k, hk, hxs⟩ := argLocs_regs bytes
      rw [hxs]
      exact ⟨xs_nodup k, xsArg k hk⟩
    · obtain ⟨k, hk, hxs⟩ := argLocs_regs bytes
      have hcnt := fun r => sretFold_count r s.params (#[], (argLocs bytes).1)
      simp only [List.toList_toArray, hxs] at hcnt
      have h8 : ((List.range k).map Reg.x).count (.x 8) = 0 :=
        List.count_eq_zero.mpr (by simp; omega)
      have e0 : locRegs ([] : List ArgLoc) = [] := rfl
      refine ⟨nodup_of_count_le_one fun r => ?_, fun r hr => ?_⟩
      · have := hcnt r
        have hx := count_le_one_of_nodup (xs_nodup k) r
        rw [e0, List.count_nil] at this
        by_cases hr : r = .x 8
        · subst hr; simp only [if_true] at this; omega
        · simp only [hr, if_false] at this; omega
      · have hpos := List.count_pos_iff.mpr hr
        have := hcnt r
        rw [e0, List.count_nil] at this
        by_cases hr8 : r = .x 8
        · exact ⟨8, by omega, hr8⟩
        · simp only [hr8, if_false] at this
          have : 0 < ((List.range k).map Reg.x).count r := by omega
          exact xsArg k hk r (List.count_pos_iff.mp this)

/-! ## The entry block's `Args` -/

theorem zip_fst_sub {α β : Type} : ∀ (l1 : List α) (l2 : List β), ((l1.zip l2).map Prod.fst).Sublist l1
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by simpa using (zip_fst_sub l1 l2).cons₂ a

theorem zip_snd_sub {α β : Type} : ∀ (l1 : List α) (l2 : List β), ((l1.zip l2).map Prod.snd).Sublist l2
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by simpa using (zip_snd_sub l1 l2).cons₂ b

/-- The `(register, vreg)` pairs of the register-passed entry parameters. -/
def entryD (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)) : List (Reg × Nat) :=
  E.filterMap fun q => match q.1.2 with
    | .reg p => some (p, q.1.1.1)
    | .stack _ => none

theorem entryD_sub : ∀ (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)),
    ((entryD E).map (·.1)).Sublist (locRegs (E.map (·.1.2))) ∧
      ((entryD E).map (·.2)).Sublist (E.map (·.1.1.1))
  | [] => by simp [entryD, locRegs]
  | q :: E => by
    obtain ⟨h1, h2⟩ := entryD_sub E
    obtain ⟨⟨⟨v, ty⟩, l⟩, b⟩ := q
    cases l with
    | reg p =>
      simp only [entryD, List.filterMap_cons, List.map_cons, locRegs] at h1 h2 ⊢
      exact ⟨h1.cons₂ _, h2.cons₂ _⟩
    | stack o =>
      simp only [entryD, List.filterMap_cons, List.map_cons, locRegs] at h1 h2 ⊢
      exact ⟨h1, h2.cons _⟩

theorem entryRegs_eq (R : Reg → Reg) : ∀ (E : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)),
    (∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int) →
    E.filterMap (entryRegOf R) = argPairs (entryD E)
  | [], _ => rfl
  | q :: E, h => by
    have ih := entryRegs_eq R E (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    obtain ⟨⟨⟨v, ty⟩, l⟩, b⟩ := q
    have hv := h _ List.mem_cons_self
    cases l with
    | reg p =>
      simp only [List.filterMap_cons, entryRegOf, entryD, argPairs, List.map_cons] at ih hv ⊢
      rw [hv, ih]
    | stack o =>
      simp only [List.filterMap_cons, entryRegOf, entryD] at ih ⊢
      exact ih

theorem params3_sub {α β γ δ : Type} (P : List (α × β)) (L : List γ) (Bs : List δ) :
    (((P.zip L).zip Bs).map (·.1.2)).Sublist L ∧
      (((P.zip L).zip Bs).map (·.1.1.1)).Sublist (P.map (·.1)) := by
  have e1 : (((P.zip L).zip Bs).map (·.1.2)) = (((P.zip L).zip Bs).map Prod.fst).map Prod.snd := by
    simp
  have e2 : (((P.zip L).zip Bs).map (·.1.1.1)) =
      ((((P.zip L).zip Bs).map Prod.fst).map Prod.fst).map (·.1) := by
    simp
  rw [e1, e2]
  exact ⟨((zip_fst_sub _ _).map _).trans (zip_snd_sub _ _),
    (((zip_fst_sub _ _).map _).trans (zip_fst_sub _ _)).map _⟩

/-- **The entry block's `Args`**, renamed by `R` fixing its parameters' vregs. -/
theorem spillInstOk_entryArgs {f : Clif.Function} {R : Reg → Reg} {B : Clif.Block}
    (hsig : (f.sig.params.filter (·.purpose == .sret)).length ≤ 1)
    (hpar : (B.params.map (·.1)).Nodup)
    (hR : ∀ x ∈ B.params.map (·.1), R (.vreg x .int) = .vreg x .int) :
    SpillInstOk (.args (entryRegs f R B)) := by
  have he : entryRegs f R B = argPairs (entryD (entryParams f B)) := by
    unfold entryRegs
    refine entryRegs_eq R _ (fun q hq => hR _ ?_)
    unfold entryParams at hq
    exact List.mem_map_of_mem (List.of_mem_zip (List.of_mem_zip hq).1).1
  rw [he]
  obtain ⟨hnd, harg⟩ := locsOf_regs hsig
  obtain ⟨s1, s2⟩ := entryD_sub (entryParams f B)
  obtain ⟨hE1, hE2⟩ : ((entryParams f B).map (·.1.2)).Sublist (locsOf f.sig) ∧
      ((entryParams f B).map (·.1.1.1)).Sublist (B.params.map (·.1)) := by
    unfold entryParams; exact params3_sub _ _ _
  have r1 := s1.trans (hE1.filterMap _)
  refine spillInstOk_args (fun q hq => harg q.1 (r1.subset (List.mem_map_of_mem hq)))
    (hnd.sublist r1) (hpar.sublist (s2.trans hE2))

/-! ## `try_call` -/

/-- A `try_call`'s `try_call_info` never clobbers everything: its signature is `system_v`. -/
theorem tryInfo_clobberAll {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} {ls : List Label} {info : TryInfo}
    (he : exnTableOpnd f et = .ok (sig, items)) (hi : tryInfoOf sig items ls = some info) :
    info.clobberAll = false := by
  have hcc : sig.callConv = none ∨ sig.callConv = some .systemV := by
    unfold exnTableOpnd at he
    cases hs : f.sigDecls.lookup et.sig with
    | none => simp [hs] at he
    | some sig' =>
      simp only [hs] at he
      split at he
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at he
      · rename_i hcc
        simp only [bind, Except.bind, pure, Except.pure] at he
        split at he
        · cases he
        · simp only [Except.ok.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, -⟩ := he
          simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, Option.isNone_iff_eq_none,
            beq_iff_eq] at hcc
          exact hcc
  unfold tryInfoOf at hi
  split at hi
  · cases hi
  · cases hi
    rcases hcc with h | h <;> simp [h]

/-! ## The ISLE runs -/

/-- The instructions emitted from `s` to `s'` have, where they are control forms, the control
shapes with defs `≥ N`. -/
def CtlSince (N : Nat) (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.isCtl = true → CtlShape N m

/-- **The ISLE inversion**: on input in scope, every ISLE run of the driver (a
statement's `lower`, a terminator's `lower`/`lower_branch`, a `try_call`'s `lower_branch`) from
a state above every value's vreg emits only control forms of the shapes `CtlShape`, with defs
above every value's vreg. The `try_call` is a terminator of `f` (`∃ B ∈ f.blocks, B.term = t`):
without it the statement is false (an unused signature declaration with two `sret` parameters
on a `try_call_indirect` gives a call with `x8` twice, rule 1036), and the driver only lowers
`f`'s own terminators. Proven: `iselCtlHyp` (`IselShpDriver`). -/
def IselCtlHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) → CtlSince ctx.valDef.size s s') ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) → CtlSince ctx.valDef.size s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      CtlSince ctx.valDef.size { st1 with emitted := #[] } s')

/-! ## Assembly -/

/-- The renaming fixes the vregs that are no alias keys. -/
theorem resolve_fix (al : List (Nat × Nat)) {n : Nat} (hn : ∀ o, (n, o) ∉ al) :
    chaseF (fun n => ((aliasArr al)[n]?).join) ((aliasArr al).size + 1) n = n := by
  apply chaseF_none
  cases h : ((aliasArr al)[n]?).join with
  | none => rfl
  | some o => exact absurd ((faithful_arr al).some n o h) (hn o)

/-- A renamed control shape with fixed defs meets `SpillInstOk`. -/
theorem spillInstOk_renamed {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {N : Nat}
    (hfix : ∀ n, N ≤ n → gn n = n) {m : MInst} (h : CtlShape N m) : SpillInstOk (m.mapRegs R) :=
  spillInstOk_mapRegs hg (spillInstOk_of_ctlShape h)
    (fun ops hops o ho hd => hfix _ (ctlShape_defs h ops hops o ho hd))

/-- The members of `vcBlocksOf` with the renaming named. -/
theorem mem_vcBlocksOf' {f : Clif.Function} {bl : List BLow} {vb : VBlock}
    (h : vb ∈ (vcBlocksOf f bl).toList) :
    (∃ bi B L, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1))
        (rawBlock f bl bi B)) ∨
    (∃ B L e, B ∈ f.blocks ∧ e ∈ edgeBlocks f B L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e) := by
  simp only [vcBlocksOf, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
  · have := List.mem_zipIdx_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at this
    exact .inl ⟨p.2, p.1.1, p.1.2, this.1, this.2, rfl⟩
  · exact .inr ⟨p.1, p.2, vb0, (List.of_mem_zip hp).1, he, rfl⟩

theorem isCtl_load (b n : Nat) (off : Int) (fl : Clif.MemFlags) :
    (MInst.load (loadOpOfBytes b) (.vreg n .int) (.fpOffset off) fl).isCtl = false := rfl

/-- **`CtlSpillHyp` from the ISLE inversion**, for input whose signatures pass the
end-to-end subset's ABI check. -/
theorem ctlSpillHyp_of (hI : IselCtlHyp) {f : Clif.Function} {vc : VCode}
    (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f) (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := hI f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  -- the alias renaming
  let al := aliasOf f bl
  let R := lowerFunction.resolve (aliasArr al) ((aliasArr al).size + 1)
  let gn := chaseF (fun n => ((aliasArr al)[n]?).join) ((aliasArr al).size + 1)
  have hg : VRenaming R gn := ⟨resolve_vreg _ _, fun r hr => by
    cases r with
    | vreg n c => exact absurd rfl (hr n c)
    | _ => rfl⟩
  have hkey : ∀ n o, (n, o) ∈ al → n < ctx.valDef.size := by
    intro n o hm
    have := (aliasOf_keys f bl).subset (List.mem_map_of_mem (f := (·.1)) hm)
    exact hN ▸ (hcf.vals n this).1
  have hfix : ∀ n, ctx.valDef.size ≤ n → gn n = n := fun n hn =>
    resolve_fix al (fun o hm => absurd (hkey n o hm) (by omega))
  intro vb hvb' i hi hct
  rw [hvb] at hvb'
  rcases mem_vcBlocksOf' hvb' with ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩
  · have hi' : i ∈ ((rawBlock f bl bi B).insts.map (MInst.mapRegs R)).toList := hi
    rw [rawBlock_insts] at hi'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi'
    rcases hi' with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · -- the entry block's `Args` and parameter loads
      unfold pre at hpre
      split at hpre
      · rename_i B0 hB0
        simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · have hB0m : B0 ∈ f.blocks := List.mem_of_getElem? hB0
          have hvd := hd.ssa
          have hpar : (B0.params.map (·.1)).Nodup := by
            unfold valueDefs at hvd
            have := (List.pairwise_flatMap.mp hvd).1 B0 hB0m
            exact (List.nodup_append.mp this).1
          refine spillInstOk_entryArgs (sret_le_of_sigAbiOk ha.1.1) hpar (fun x hx => ?_)
          show lowerFunction.resolve _ _ (Reg.vreg x .int) = _
          rw [resolve_vreg]
          congr 1
          refine resolve_fix al (fun o hm => ?_)
          obtain ⟨B', hB', stm, hstm, hr⟩ := aliasOf_key hm
          exact param_not_result hvd hB0m hB' hx (List.mem_flatMap.mpr ⟨stm, hstm, hr⟩)
        · simp only [entryLoads, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOf at hq
          split at hq
          · cases hq; exact absurd hct Bool.false_ne_true
          · cases hq
      · simp at hpre
    · -- a statement's segment
      unfold seg at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, rfl⟩ := hm
        rw [isCtl_mapRegs] at hct
        rcases hm with hm | hm
        · obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
          obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
          obtain ⟨tr, hrun⟩ := hc j sl hsl
          rw [hstart bi L hL] at hrun
          have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
          obtain ⟨ms, hms, hsh⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
          rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
          rw [hms] at hm
          exact spillInstOk_renamed hg hfix (hsh m (by simpa using hm) hct)
        · obtain ⟨s, a, b, rfl⟩ := mem_extraOf hm
          cases hct
      · simp at hm
    · -- the terminator's segment
      unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m, hm, rfl⟩ := htseg
      rw [isCtl_mapRegs] at hct
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
      cases ht : B.term.isTry with
      | false =>
        obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
        obtain ⟨ms, hms, hsh⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hdat hge hc
        rw [htst] at hms
        rw [htl] at hm
        simp only [fixTry, hms] at hm
        exact spillInstOk_renamed hg hfix (hsh m (by simpa using hm) hct)
      | true =>
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
        obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
        obtain ⟨ms, hms, hsh⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het ⟨B, List.mem_of_getElem? hB, rfl⟩ hdat hex hge hreg hc
        simp only [Array.empty_append] at hms
        rw [hT'] at hm
        simp only [fixTry, tryFix, hms, List.toList_toArray] at hm
        have hcl := tryInfo_clobberAll hex hinfo
        split at hm
        · rename_i c hlast
          rcases List.mem_append.mp hm with hm | hm
          · exact spillInstOk_renamed hg hfix (hsh m (List.dropLast_subset _ hm) hct)
          · simp only [List.mem_singleton] at hm
            subst hm
            have hcm : MInst.call c ∈ ms := List.mem_of_getLast? hlast
            have hsc := hsh _ hcm rfl
            refine spillInstOk_mapRegs hg (spillInstOk_tryCall_of_call hcl (spillInstOk_of_ctlShape hsc))
              (fun ops hops o ho hdf => hfix _ (ctlShape_defs hsc ops
                ((operands_tryCall_call c T.info).symm.trans hops) o ho hdf))
        · exact spillInstOk_renamed hg hfix (hsh m hm hct)
  · obtain ⟨tl, hie⟩ := edgeBlocks_insts he
    simp only [fixBlock, hie] at hi
    simp at hi
    subst hi
    exact spillInstOk_jump tl

end Backend.Proof.Spill
