import FV.Backend.Proof.SpillStep4Edge

/-!
# Branch arguments of the spill allocation (V4 (a), step 4)

`argMoves_runs`: the two-phase parallel copy `spillArgMoves` (every argument through the scratch
register into its temporary slot, then every temporary into its parameter's home) leaves each
parameter's home with its argument's symbols, every other home and every save slot untouched.
`edge_args`: after the copy and the `jump`, the checker's edge (`parCopy`) feeds the target's
in-state.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-- The first phase of `spillArgMoves`, per argument: its home into its temporary. -/
def p1 (h : Homes) (x : (Reg × Reg) × Nat) : List RItem :=
  [.move (spillHome h x.1.1.homeNum x.1.1.homeCls) (.reg (spillScratch x.1.1.homeCls)),
   .move (.reg (spillScratch x.1.1.homeCls)) (.stack (h.size + x.2) x.1.1.homeCls)]

/-- The second phase of `spillArgMoves`, per parameter: its temporary into its home. -/
def p2 (h : Homes) (x : (Reg × Reg) × Nat) : List RItem :=
  [.move (.stack (h.size + x.2) x.1.2.homeCls) (.reg (spillScratch x.1.2.homeCls)),
   .move (.reg (spillScratch x.1.2.homeCls)) (spillHome h x.1.2.homeNum x.1.2.homeCls)]

theorem spillArgMoves_eq (h : Homes) (vb tb : VBlock) :
    spillArgMoves h vb tb =
      ((vb.branchArgs.toList.zip tb.params.toList).zipIdx.flatMap (p1 h)) ++
      ((vb.branchArgs.toList.zip tb.params.toList).zipIdx.flatMap (p2 h)) := rfl

theorem mapM_vregNum : ∀ (l : List Reg), (∀ r ∈ l, ∃ n c, r = .vreg n c) →
    l.mapM vregNum = .ok (l.map Reg.homeNum)
  | [], _ => rfl
  | r :: l, h => by
    obtain ⟨n, c, rfl⟩ := h r List.mem_cons_self
    rw [List.mapM_cons, mapM_vregNum l (fun r hr => h r (.tail _ hr))]
    rfl

section
variable {c : CheckCtx} {vc : VCode} (hsl : c.rf.spillSlots = (spillHomes vc).size + maxArgs vc)
  {vb : VBlock} {k : Nat} (hkn : k ≠ vb.insts.size)
include hsl hkn

theorem phase1_runs : ∀ (L : List (Reg × Reg)) (s : Nat) (a0 : AState),
    (∀ x ∈ L, ∃ n, (spillHomes vc)[(x.1.homeNum, x.1.homeCls)]? = some n) →
    s + L.length ≤ maxArgs vc → a0.size = stN vc →
    Runs c vb k ((L.zipIdx s).flatMap (p1 (spillHomes vc))) a0 fun k' a' => k' = k ∧
      a'.size = stN vc ∧
      (∀ l, (∀ cl, l ≠ .reg (spillScratch cl)) →
        (∀ j cl, s ≤ j → l ≠ .stack ((spillHomes vc).size + j) cl) → a'.get l = a0.get l) ∧
      ∀ j x, L[j]? = some x → a'.get (.stack ((spillHomes vc).size + (s + j)) x.1.homeCls) =
        a0.get (spillHome (spillHomes vc) x.1.homeNum x.1.homeCls)
  | [], s, a0, _, _, hsz => Runs.nil ⟨rfl, hsz, fun _ _ _ => rfl, fun j x h => by simp at h⟩
  | x :: L, s, a0, hh, hlen, hsz => by
    obtain ⟨n, hn⟩ := hh x List.mem_cons_self
    have hnl := spillHomes_lt vc hn
    have hscr := scratch_ok x.1.homeCls
    simp only [List.length_cons] at hlen
    obtain ⟨is, his, hislt⟩ := reg_index_lt (vc := vc) hscr.1
    obtain ⟨it, hit, hitlt⟩ := stack_index_lt (vc := vc) (n := (spillHomes vc).size + s)
      (c := x.1.homeCls) (by omega)
    obtain ⟨a1, ha1⟩ : ∃ a1, a1 = a0.put (.reg (spillScratch x.1.homeCls))
        (a0.get (spillHome (spillHomes vc) x.1.homeNum x.1.homeCls)) := ⟨_, rfl⟩
    obtain ⟨a2, ha2⟩ : ∃ a2, a2 = a1.put (.stack ((spillHomes vc).size + s) x.1.homeCls)
        (a1.get (.reg (spillScratch x.1.homeCls))) := ⟨_, rfl⟩
    have hsz1 : a1.size = stN vc := by rw [ha1, size_put, hsz]
    have hsz2 : a2.size = stN vc := by rw [ha2, size_put, hsz1]
    rw [List.zipIdx_cons, List.flatMap_cons,
      show p1 (spillHomes vc) (x, s) = [RItem.move (spillHome (spillHomes vc) x.1.homeNum x.1.homeCls)
        (.reg (spillScratch x.1.homeCls))] ++ [RItem.move (.reg (spillScratch x.1.homeCls))
        (.stack ((spillHomes vc).size + s) x.1.homeCls)] from rfl, List.append_assoc]
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a1) (Runs.move hkn ?_ ⟨rfl, ha1.symm⟩)
      fun k1 b1 ⟨e1, e2⟩ => ?_
    · rw [spillHome_eq hn]
      exact checkMove_load c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b1
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a2) (Runs.move hkn ?_ ⟨rfl, ha2.symm⟩)
      fun k1 b2 ⟨e1, e2⟩ => ?_
    · exact checkMove_store c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b2
    refine (phase1_runs L (s + 1) a2 (fun y hy => hh y (.tail _ hy)) (by omega) hsz2).mono
      fun k' a' ⟨f1, f2, f3, f4⟩ => ⟨f1, f2, ?_, ?_⟩
    · intro l hl1 hl2
      rw [f3 l hl1 (fun j cl hj => hl2 j cl (by omega)), ha2,
        get_put_ne (Ne.symm (hl2 s _ (Nat.le_refl _))), ha1, get_put_ne (Ne.symm (hl1 _))]
    · intro j y hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, f3 _ (fun cl he => by cases he) (fun j cl hj he => by injection he with h1; omega), ha2,
          get_put_self hit (by rw [hsz1]; exact hitlt), ha1,
          get_put_self his (by rw [hsz]; exact hislt)]
      | succ j =>
        have hj' : L[j]? = some y := by simpa using hj
        rw [show s + (j + 1) = s + 1 + j by omega, f4 j y hj']
        obtain ⟨ny, hny⟩ := hh y (.tail _ (List.mem_of_getElem? hj'))
        have := spillHomes_lt vc hny
        rw [spillHome_eq hny, ha2, get_put_ne (by intro he; injection he with h1; omega), ha1,
          get_put_ne (by intro he; cases he)]

theorem phase2_runs : ∀ (L : List (Reg × Reg)) (s : Nat) (a0 : AState),
    (∀ x ∈ L, ∃ n, (spillHomes vc)[(x.2.homeNum, x.2.homeCls)]? = some n) →
    (L.map (·.2.homeNum)).Nodup → s + L.length ≤ maxArgs vc → a0.size = stN vc →
    Runs c vb k ((L.zipIdx s).flatMap (p2 (spillHomes vc))) a0 fun k' a' => k' = k ∧
      a'.size = stN vc ∧
      (∀ l, (∀ cl, l ≠ .reg (spillScratch cl)) →
        (∀ x ∈ L, l ≠ spillHome (spillHomes vc) x.2.homeNum x.2.homeCls) → a'.get l = a0.get l) ∧
      ∀ j x, L[j]? = some x → a'.get (spillHome (spillHomes vc) x.2.homeNum x.2.homeCls) =
        a0.get (.stack ((spillHomes vc).size + (s + j)) x.2.homeCls)
  | [], s, a0, _, _, _, hsz => Runs.nil ⟨rfl, hsz, fun _ _ _ => rfl, fun j x h => by simp at h⟩
  | x :: L, s, a0, hh, hnd, hlen, hsz => by
    obtain ⟨n, hn⟩ := hh x List.mem_cons_self
    have hnl := spillHomes_lt vc hn
    have hscr := scratch_ok x.2.homeCls
    simp only [List.length_cons] at hlen
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨is, his, hislt⟩ := reg_index_lt (vc := vc) hscr.1
    obtain ⟨ih, hih, hihlt⟩ := home_index_lt hn
    obtain ⟨a1, ha1⟩ : ∃ a1, a1 = a0.put (.reg (spillScratch x.2.homeCls))
        (a0.get (.stack ((spillHomes vc).size + s) x.2.homeCls)) := ⟨_, rfl⟩
    obtain ⟨a2, ha2⟩ : ∃ a2, a2 = a1.put (.stack n x.2.homeCls)
        (a1.get (.reg (spillScratch x.2.homeCls))) := ⟨_, rfl⟩
    have hsz1 : a1.size = stN vc := by rw [ha1, size_put, hsz]
    have hsz2 : a2.size = stN vc := by rw [ha2, size_put, hsz1]
    rw [List.zipIdx_cons, List.flatMap_cons,
      show p2 (spillHomes vc) (x, s) = [RItem.move (.stack ((spillHomes vc).size + s) x.2.homeCls)
        (.reg (spillScratch x.2.homeCls))] ++ [RItem.move (.reg (spillScratch x.2.homeCls))
        (.stack n x.2.homeCls)] by simp [p2, spillHome_eq hn], List.append_assoc]
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a1) (Runs.move hkn ?_ ⟨rfl, ha1.symm⟩)
      fun k1 b1 ⟨e1, e2⟩ => ?_
    · exact checkMove_load c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b1
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a2) (Runs.move hkn ?_ ⟨rfl, ha2.symm⟩)
      fun k1 b2 ⟨e1, e2⟩ => ?_
    · exact checkMove_store c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b2
    -- the homes of the other parameters differ from this one's
    have hdist : ∀ y ∈ L, Loc.stack n x.2.homeCls ≠ spillHome (spillHomes vc) y.2.homeNum y.2.homeCls := by
      intro y hy he
      obtain ⟨ny, hny⟩ := hh y (.tail _ hy)
      rw [spillHome_eq hny] at he
      injection he with e1 e2
      rw [← e1, ← e2] at hny
      have := spillHomes_inj vc hn hny
      injection this with ev
      exact hnd.1 (ev ▸ List.mem_map_of_mem hy)
    refine (phase2_runs L (s + 1) a2 (fun y hy => hh y (.tail _ hy)) hnd.2 (by omega)
      hsz2).mono fun k' a' ⟨f1, f2, f3, f4⟩ => ⟨f1, f2, ?_, ?_⟩
    · intro l hl1 hl2
      rw [f3 l hl1 (fun y hy => hl2 y (.tail _ hy)), ha2,
        get_put_ne (by rw [← spillHome_eq hn]; exact Ne.symm (hl2 x List.mem_cons_self)), ha1,
        get_put_ne (Ne.symm (hl1 _))]
    · intro j y hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, spillHome_eq hn, f3 _ (fun cl he => by cases he) hdist, ha2,
          get_put_self hih (by rw [hsz1]; exact hihlt), ha1,
          get_put_self his (by rw [hsz]; exact hislt)]
      | succ j =>
        have hj' : L[j]? = some y := by simpa using hj
        rw [show s + (j + 1) = s + 1 + j by omega, f4 j y hj', ha2,
          get_put_ne (by intro he; injection he with h1; omega), ha1,
          get_put_ne (by intro he; cases he)]

end

section
variable {vc : VCode} {succs preds : Array (Array Nat)} {D : Nat → Nat → Bool}

/-- **The argument copies**: every parameter's home gets its argument's symbols; every other home
of an available vreg keeps it; the save slots keep their entry values. -/
theorem argMoves_runs (hloc : SpillLocalOk vc) {c : CheckCtx}
    (hsl : c.rf.spillSlots = (spillHomes vc).size + maxArgs vc) {b t : Nat} {vb tb : VBlock}
    (hvb : vc.blocks[b]? = some vb) (htb : vc.blocks[t]? = some tb)
    (hsz : tb.params.size = vb.branchArgs.size)
    (hcls : ∀ (kk : Nat) (a p : Reg), vb.branchArgs[kk]? = some a → tb.params[kk]? = some p →
      ∃ x y c, a = .vreg x c ∧ p = .vreg y c)
    (hnd : (tb.params.toList.map Reg.homeNum).Nodup) {k : Nat} (hkn : k ≠ vb.insts.size)
    {A : Nat → Bool} {a : AState} (hg : Good vc A a) :
    Runs c vb k (spillArgMoves (spillHomes vc) vb tb) a fun k' a' => k' = k ∧ a'.size = stN vc ∧
      (∀ r ∈ calleeSaved, Sym.entry r ∈ a'.get (.save r)) ∧
      (∀ v cl n, A v = true → vc.classes[v]? = some cl → (spillHomes vc)[(v, cl)]? = some n →
        v ∉ tb.params.toList.map Reg.homeNum → Sym.vreg v ∈ a'.get (.stack n cl)) ∧
      (∀ (kk : Nat) (ar p : Reg), vb.branchArgs[kk]? = some ar → tb.params[kk]? = some p → A ar.homeNum = true →
        Sym.vreg ar.homeNum ∈ a'.get (spillHome (spillHomes vc) p.homeNum p.homeCls)) := by
  have hlenL : (vb.branchArgs.toList.zip tb.params.toList).length ≤ maxArgs vc := by
    have := maxArgs_ge vc hvb
    simp only [List.length_zip, Array.length_toList]
    unfold maxArgs
    omega
  have hargL : ∀ x ∈ vb.branchArgs.toList.zip tb.params.toList, x.1 ∈ vb.branchArgs.toList ∧
      x.2 ∈ tb.params.toList := fun x hx => ⟨List.of_mem_zip hx |>.1, List.of_mem_zip hx |>.2⟩
  have hmap2 : (vb.branchArgs.toList.zip tb.params.toList).map (·.2.homeNum) =
      tb.params.toList.map Reg.homeNum := by
    rw [show (fun x : Reg × Reg => x.2.homeNum) = Reg.homeNum ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp [hsz])]
  rw [spillArgMoves_eq]
  refine Runs.append (phase1_runs hsl hkn _ 0 a (fun x hx => ?_) (by omega) hg.size)
    fun k1 a1 ⟨e1, sz1, fr1, val1⟩ => ?_
  · obtain ⟨n, cl, he, -, m, hm⟩ := regFacts hloc hvb (List.mem_append_right _ (hargL x hx).1)
    rw [he]
    exact ⟨m, hm⟩
  subst e1
  refine (phase2_runs hsl hkn _ 0 a1 (fun x hx => ?_) (by rw [hmap2]; exact hnd) (by omega)
    sz1).mono fun k2 a2 ⟨e2, sz2, fr2, val2⟩ => ⟨e2, sz2, ?_, ?_, ?_⟩
  · obtain ⟨n, cl, he, -, m, hm⟩ := regFacts hloc htb (List.mem_append_left _ (hargL x hx).2)
    rw [he]
    exact ⟨m, hm⟩
  · intro r hr
    rw [fr2 _ (fun _ he => by cases he) (fun x hx he => by
        obtain ⟨n, cl, hp, -, m, hm⟩ := regFacts hloc htb (List.mem_append_left _ (hargL x hx).2)
        rw [hp] at he
        simp [spillHome] at he),
      fr1 _ (fun _ he => by cases he) (fun _ _ _ he => by cases he)]
    exact hg.save r hr
  · intro v cl n hv hc hn hnp
    have hnl := spillHomes_lt vc hn
    rw [fr2 _ (fun _ he => by cases he) (fun x hx he => ?_),
      fr1 _ (fun _ he => by cases he) (fun j cl' _ he => by injection he with h1; omega)]
    · exact hg.home v cl n hv hc hn
    · obtain ⟨y, cy, hp, -, m, hm⟩ := regFacts hloc htb (List.mem_append_left _ (hargL x hx).2)
      rw [hp] at he
      simp only [Reg.homeNum, Reg.homeCls, spillHome_eq hm] at he
      injection he with e1 e2
      rw [← e1, ← e2] at hm
      have := spillHomes_inj vc hn hm
      injection this with ev
      exact hnp (by rw [ev]; exact List.mem_map.mpr ⟨x.2, (hargL x hx).2, by rw [hp]; rfl⟩)
  · intro kk ar p har hp hA
    have hz : (vb.branchArgs.toList.zip tb.params.toList)[kk]? = some (ar, p) :=
      List.getElem?_zip_eq_some.mpr ⟨by simpa using har, by simpa using hp⟩
    obtain ⟨x, y, cl, rfl, rfl⟩ := hcls kk ar p har hp
    have h2 := val2 kk _ hz
    have h1 := val1 kk _ hz
    simp only [Nat.zero_add, Reg.homeCls, Reg.homeNum] at h1 h2 hA ⊢
    rw [h2, h1]
    obtain ⟨n', cl', he, hc, m, hm⟩ := regFacts hloc hvb
      (List.mem_append_right _ (List.mem_of_getElem? (by simpa using har)))
    injection he with e1 e2
    subst e1 e2
    rw [spillHome_eq hm]
    exact hg.home _ _ m hA hc hm

/-- **An edge with arguments** (a `jump`'s): after the copies and the `jump`, the checker's
parallel copy feeds the target's in-state. -/
theorem edge_args (hcfg : vc.cfg = .ok (succs, preds)) (hloc : SpillLocalOk vc)
    (hav : SpillAvail vc D) {c : CheckCtx} (hcvc : c.vc = vc) (hcs : c.succs = succs)
    {b t : Nat} {vb tb : VBlock} (hvb : vc.blocks[b]? = some vb) (hss : succs[b]? = some #[t])
    (htb : vc.blocks[t]? = some tb) (hba : vb.branchArgs ≠ #[]) {i : MInst}
    (hT : vb.insts.back? = some i) (hops : i.operands = .ok #[])
    (hsz : tb.params.size = vb.branchArgs.size) (hnd : (tb.params.toList.map Reg.homeNum).Nodup)
    {A : Nat → Bool} (hA : availAt vb.insts (availStart vc succs preds D b) vb.insts.size = A)
    {a : AState} (hsv : ∀ r ∈ calleeSaved, Sym.entry r ∈ a.get (.save r))
    (hnp : ∀ v cl n, A v = true → vc.classes[v]? = some cl → (spillHomes vc)[(v, cl)]? = some n →
      v ∉ tb.params.toList.map Reg.homeNum → Sym.vreg v ∈ a.get (.stack n cl))
    (hpa : ∀ (kk : Nat) (ar p : Reg), vb.branchArgs[kk]? = some ar → tb.params[kk]? = some p → A ar.homeNum = true →
      Sym.vreg ar.homeNum ∈ a.get (spillHome (spillHomes vc) p.homeNum p.homeCls)) :
    ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e, c.edge b s a = .ok e ∧
      (inState vc succs preds D s).le e = true := by
  intro s hs
  have hE := hloc.2.2 succs preds hcfg
  rw [hcs, hss] at hs
  simp only [Option.getD_some, List.mem_singleton] at hs
  subst hs
  have ht : s ∈ (#[s] : Array Nat).toList := by simp
  have hs0 : s ≠ 0 := fun h => preds_empty hcfg (h ▸ hE.entry.2.1) hss ht
  have hnd0 : i.normalDead = none := by
    unfold MInst.normalDead
    split
    · rename_i info ti
      exact absurd (hE.tryEdge b vb info ti #[s] s hvb hT).1 hba
    · rfl
  have hF : c.edgeForget b s a = a := by
    rcases edgeForget_cases (s := s) hcvc hvb hT hops a with h | ⟨jn, n, h, -⟩
    · exact h
    · rw [hnd0] at h; cases h
  have hpv : ∀ r ∈ tb.params.toList, ∃ n c, r = .vreg n c := fun r hr =>
    let ⟨n, c, h, _⟩ := regFacts hloc htb (List.mem_append_left _ hr); ⟨n, c, h⟩
  have hxv : ∀ r ∈ vb.branchArgs.toList, ∃ n c, r = .vreg n c := fun r hr =>
    let ⟨n, c, h, _⟩ := regFacts hloc hvb (List.mem_append_right _ hr); ⟨n, c, h⟩
  have hC : c.edgeCopy b s a = .ok (a.parCopy (tb.params.toList.map Reg.homeNum)
      (vb.branchArgs.toList.map Reg.homeNum)) := by
    unfold CheckCtx.edgeCopy
    rw [hcvc, hvb, htb]
    have hie : vb.branchArgs.isEmpty = false := by
      rw [Bool.eq_false_iff]; intro h; exact hba (Array.isEmpty_iff.mp h)
    simp only [ensure_true (b := vb.branchArgs.size == tb.params.size) (by simp [hsz]), hie,
      mapM_vregNum _ hpv, mapM_vregNum _ hxv, ensure_true (b := decide _) (decide_eq_true hnd),
      bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, by unfold CheckCtx.edge; rw [hF]; exact hC, le_of_mem fun l x hx => ?_⟩
  have hx' := (mem_get_mkState hx).1
  cases l with
  | reg r =>
    rcases inReg_mem hx' with ⟨h0, -, -⟩ | ⟨y, hy, -, -⟩
    · exact absurd h0 hs0
    · obtain ⟨p, vbp, ssp, j, hp, hvbp, hssp, hj, hyt⟩ := entryPairs_spec hy
      obtain ⟨rfl, -⟩ := preds_single hcfg hss (j := 0) (by simp) hp
      rw [hvb] at hvbp
      cases hvbp
      obtain ⟨T', ops', hT', -, hops', hyk, -⟩ := termEdgeDefs_spec hyt
      rw [hT] at hT'
      cases hT'
      rw [hops] at hops'
      cases hops'
      have := (mem_keptPairs hyk).1
      simp at this
  | save r =>
    obtain ⟨-, hr, rfl⟩ := inSave_mem hx'
    exact mem_parCopy_keep (hsv r hr) fun _ _ h => by cases h
  | stack n cl =>
    obtain ⟨v, rfl, hn, hc, hD⟩ := inStack_mem hx'
    have hea := hav.edges succs preds hcfg b vb #[s] s tb hvb hss ht htb v hD
    rw [hA] at hea
    unfold edgeAvail at hea
    cases hidx : (tb.params.toList.map Reg.homeNum).idxOf? v with
    | none =>
      rw [hidx] at hea
      simp only at hea
      have hv : v ∉ tb.params.toList.map Reg.homeNum := List.idxOf?_eq_none_iff.mp hidx
      exact mem_parCopy_keep (hnp v cl n hea hc hn hv) fun p hp he => by
        injection he with he; subst he; exact hv hp
    | some kk =>
      rw [hidx] at hea
      simp only at hea
      obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.mp hidx
      cases har : vb.branchArgs[kk]? with
      | none => rw [har] at hea; cases hea
      | some ar =>
      rw [har] at hea
      have hkp : kk < tb.params.size := by simpa using hlt
      have hp : tb.params[kk]? = some tb.params[kk] := Array.getElem?_eq_getElem hkp
      obtain ⟨y, cy, hpy, hcy, -⟩ := regFacts hloc htb
        (List.mem_append_left _ (Array.getElem_mem_toList hkp))
      have hyv : y = v := by
        simp only [List.getElem_map, Array.getElem_toList] at hget
        rw [hpy] at hget
        exact hget
      subst hyv
      rw [hc] at hcy
      cases hcy
      have hm := hpa kk ar _ har hp hea
      rw [hpy] at hm
      simp only [Reg.homeNum, Reg.homeCls, spillHome_eq hn] at hm
      refine mem_parCopy_add (List.mem_iff_getElem?.mpr ⟨kk, List.getElem?_zip_eq_some.mpr ⟨?_, ?_⟩⟩) hm
      · rw [List.getElem?_map, Array.getElem?_toList, hp, hpy]; rfl
      · rw [List.getElem?_map, Array.getElem?_toList, har]; rfl

end

end Backend.Proof.Spill
