import FV.Backend.Proof.PerEdgeSpillHomes
import FV.Backend.Proof.SpillStep4Args

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Abstract-state size used by the actual indexed checker for this fallback. -/
def stateSizeAt (vc : VCode) (edges : Array (Array (Array Reg))) : Nat :=
  128 + 2*((spillHomesAt vc edges).size + maxArgsAt edges)
private theorem home_eq {h : SpillHomesAt} {v n : Nat} {cl : RegClass}
    (found : homeLookup h (spillHomeKeyAt v cl) = some n) : spillHomeAt h v cl = .stack n cl := by
  unfold homeLookup at found
  simp only [spillHomeAt,found,Option.getD_some]
private theorem home_lt {vc : VCode} {edges : Array (Array (Array Reg))} {key n : Nat}
    (found : homeLookup (spillHomesAt vc edges) key = some n) : n < (spillHomesAt vc edges).size :=
  (spillHomesAt_spec vc edges).valid.1 key n found
private theorem home_inj {vc : VCode} {edges : Array (Array (Array Reg))} {v w n : Nat} {c d : RegClass}
    (left : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n)
    (right : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt w d) = some n) : (v,c) = (w,d) := by
  have same := (spillHomesAt_spec vc edges).valid.2 _ _ _ left right
  obtain ⟨rfl,rfl⟩ := spillHomeKeyAt_injective same
  rfl
private theorem stack_index_lt {vc : VCode} {edges : Array (Array (Array Reg))} {n : Nat} {c : RegClass}
    (bound : n < (spillHomesAt vc edges).size+maxArgsAt edges) :
    ∃ i,(Loc.stack n c).index = some i ∧ i < stateSizeAt vc edges := by
  cases c <;> simp only [Loc.index,stateSizeAt] <;> exact ⟨_,rfl,by omega⟩
private theorem reg_index_lt {vc : VCode} {edges : Array (Array (Array Reg))} {r : Reg}
    (h : r.allocatable = true) : ∃ i,(Loc.reg r).index = some i ∧ i < stateSizeAt vc edges := by
  obtain ⟨i,found,bound⟩ := reg_index h
  exact ⟨i,found,by unfold stateSizeAt; omega⟩
private theorem home_index_lt {vc : VCode} {edges : Array (Array (Array Reg))} {n v : Nat} {c : RegClass}
    (found : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n) :
    ∃ i,(Loc.stack n c).index = some i ∧ i < stateSizeAt vc edges :=
  stack_index_lt (by have bound := home_lt found; omega)

/-- The first phase of `spillArgMoves`, per argument: its home into its temporary. -/
def p1 (h : SpillHomesAt) (x : (Reg × Reg) × Nat) : List RItem :=
  [.move (spillHomeAt h x.1.1.homeNum x.1.1.homeCls) (.reg (spillScratch x.1.1.homeCls)),
   .move (.reg (spillScratch x.1.1.homeCls)) (.stack (h.size + x.2) x.1.1.homeCls)]

/-- The second phase of `spillArgMoves`, per parameter: its temporary into its home. -/
def p2 (h : SpillHomesAt) (x : (Reg × Reg) × Nat) : List RItem :=
  [.move (.stack (h.size + x.2) x.1.2.homeCls) (.reg (spillScratch x.1.2.homeCls)),
   .move (.reg (spillScratch x.1.2.homeCls)) (spillHomeAt h x.1.2.homeNum x.1.2.homeCls)]

private theorem copy_eq (h : SpillHomesAt) (args params : Array Reg) :
    spillArgMovesAt h args params =
      ((args.toList.zip params.toList).zipIdx.flatMap (p1 h)) ++
      ((args.toList.zip params.toList).zipIdx.flatMap (p2 h)) := rfl


section
variable {c : CheckCtx} {vc : VCode} {edges : Array (Array (Array Reg))} (hsl : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
  {vb : VBlock} {k : Nat} (hkn : k ≠ vb.insts.size)
include hsl hkn

private theorem phase1_runs : ∀ (L : List (Reg × Reg)) (s : Nat) (a0 : AState),
    (∀ x ∈ L, ∃ n, homeLookup (spillHomesAt vc edges) (spillHomeKeyAt x.1.homeNum x.1.homeCls) = some n) →
    s + L.length ≤ maxArgsAt edges → a0.size = stateSizeAt vc edges →
    Runs c vb k ((L.zipIdx s).flatMap (p1 (spillHomesAt vc edges))) a0 fun k' a' => k' = k ∧
      a'.size = stateSizeAt vc edges ∧
      (∀ l, (∀ cl, l ≠ .reg (spillScratch cl)) →
        (∀ j cl, s ≤ j → l ≠ .stack ((spillHomesAt vc edges).size + j) cl) → a'.get l = a0.get l) ∧
      ∀ j x, L[j]? = some x → a'.get (.stack ((spillHomesAt vc edges).size + (s + j)) x.1.homeCls) =
        a0.get (spillHomeAt (spillHomesAt vc edges) x.1.homeNum x.1.homeCls)
  | [], s, a0, _, _, hsz => Runs.nil ⟨rfl, hsz, fun _ _ _ => rfl, fun j x h => by simp at h⟩
  | x :: L, s, a0, hh, hlen, hsz => by
    obtain ⟨n, hn⟩ := hh x List.mem_cons_self
    have hnl := home_lt hn
    have hscr := scratch_ok x.1.homeCls
    simp only [List.length_cons] at hlen
    obtain ⟨is, his, hislt⟩ := reg_index_lt (vc := vc) (edges := edges) hscr.1
    obtain ⟨it, hit, hitlt⟩ := stack_index_lt (vc := vc) (edges := edges) (n := (spillHomesAt vc edges).size + s)
      (c := x.1.homeCls) (by omega)
    obtain ⟨a1, ha1⟩ : ∃ a1, a1 = a0.put (.reg (spillScratch x.1.homeCls))
        (a0.get (spillHomeAt (spillHomesAt vc edges) x.1.homeNum x.1.homeCls)) := ⟨_, rfl⟩
    obtain ⟨a2, ha2⟩ : ∃ a2, a2 = a1.put (.stack ((spillHomesAt vc edges).size + s) x.1.homeCls)
        (a1.get (.reg (spillScratch x.1.homeCls))) := ⟨_, rfl⟩
    have hsz1 : a1.size = stateSizeAt vc edges := by rw [ha1, size_put, hsz]
    have hsz2 : a2.size = stateSizeAt vc edges := by rw [ha2, size_put, hsz1]
    rw [List.zipIdx_cons, List.flatMap_cons,
      show p1 (spillHomesAt vc edges) (x, s) = [RItem.move (spillHomeAt (spillHomesAt vc edges) x.1.homeNum x.1.homeCls)
        (.reg (spillScratch x.1.homeCls))] ++ [RItem.move (.reg (spillScratch x.1.homeCls))
        (.stack ((spillHomesAt vc edges).size + s) x.1.homeCls)] from rfl, List.append_assoc]
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a1) (Runs.move hkn ?_ ⟨rfl, ha1.symm⟩)
      fun k1 b1 ⟨e1, e2⟩ => ?_
    · rw [home_eq hn]
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
        have := home_lt hny
        rw [home_eq hny, ha2, get_put_ne (by intro he; injection he with h1; omega), ha1,
          get_put_ne (by intro he; cases he)]

private theorem phase2_runs : ∀ (L : List (Reg × Reg)) (s : Nat) (a0 : AState),
    (∀ x ∈ L, ∃ n, homeLookup (spillHomesAt vc edges) (spillHomeKeyAt x.2.homeNum x.2.homeCls) = some n) →
    (L.map (·.2.homeNum)).Nodup → s + L.length ≤ maxArgsAt edges → a0.size = stateSizeAt vc edges →
    Runs c vb k ((L.zipIdx s).flatMap (p2 (spillHomesAt vc edges))) a0 fun k' a' => k' = k ∧
      a'.size = stateSizeAt vc edges ∧
      (∀ l, (∀ cl, l ≠ .reg (spillScratch cl)) →
        (∀ x ∈ L, l ≠ spillHomeAt (spillHomesAt vc edges) x.2.homeNum x.2.homeCls) → a'.get l = a0.get l) ∧
      ∀ j x, L[j]? = some x → a'.get (spillHomeAt (spillHomesAt vc edges) x.2.homeNum x.2.homeCls) =
        a0.get (.stack ((spillHomesAt vc edges).size + (s + j)) x.2.homeCls)
  | [], s, a0, _, _, _, hsz => Runs.nil ⟨rfl, hsz, fun _ _ _ => rfl, fun j x h => by simp at h⟩
  | x :: L, s, a0, hh, hnd, hlen, hsz => by
    obtain ⟨n, hn⟩ := hh x List.mem_cons_self
    have hnl := home_lt hn
    have hscr := scratch_ok x.2.homeCls
    simp only [List.length_cons] at hlen
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨is, his, hislt⟩ := reg_index_lt (vc := vc) (edges := edges) hscr.1
    obtain ⟨ih, hih, hihlt⟩ := home_index_lt hn
    obtain ⟨a1, ha1⟩ : ∃ a1, a1 = a0.put (.reg (spillScratch x.2.homeCls))
        (a0.get (.stack ((spillHomesAt vc edges).size + s) x.2.homeCls)) := ⟨_, rfl⟩
    obtain ⟨a2, ha2⟩ : ∃ a2, a2 = a1.put (.stack n x.2.homeCls)
        (a1.get (.reg (spillScratch x.2.homeCls))) := ⟨_, rfl⟩
    have hsz1 : a1.size = stateSizeAt vc edges := by rw [ha1, size_put, hsz]
    have hsz2 : a2.size = stateSizeAt vc edges := by rw [ha2, size_put, hsz1]
    rw [List.zipIdx_cons, List.flatMap_cons,
      show p2 (spillHomesAt vc edges) (x, s) = [RItem.move (.stack ((spillHomesAt vc edges).size + s) x.2.homeCls)
        (.reg (spillScratch x.2.homeCls))] ++ [RItem.move (.reg (spillScratch x.2.homeCls))
        (.stack n x.2.homeCls)] by simp [p2, home_eq hn], List.append_assoc]
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a1) (Runs.move hkn ?_ ⟨rfl, ha1.symm⟩)
      fun k1 b1 ⟨e1, e2⟩ => ?_
    · exact checkMove_load c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b1
    refine Runs.append (Q := fun k' a => k' = k ∧ a = a2) (Runs.move hkn ?_ ⟨rfl, ha2.symm⟩)
      fun k1 b2 ⟨e1, e2⟩ => ?_
    · exact checkMove_store c _ (by rw [hsl]; omega) hscr.1 hscr.2
    subst k1 b2
    -- the homes of the other parameters differ from this one's
    have hdist : ∀ y ∈ L, Loc.stack n x.2.homeCls ≠ spillHomeAt (spillHomesAt vc edges) y.2.homeNum y.2.homeCls := by
      intro y hy he
      obtain ⟨ny, hny⟩ := hh y (.tail _ hy)
      rw [home_eq hny] at he
      injection he with e1 e2
      rw [← e1, ← e2] at hny
      have := home_inj hn hny
      injection this with ev
      exact hnd.1 (ev ▸ List.mem_map_of_mem hy)
    refine (phase2_runs L (s + 1) a2 (fun y hy => hh y (.tail _ hy)) hnd.2 (by omega)
      hsz2).mono fun k' a' ⟨f1, f2, f3, f4⟩ => ⟨f1, f2, ?_, ?_⟩
    · intro l hl1 hl2
      rw [f3 l hl1 (fun y hy => hl2 y (.tail _ hy)), ha2,
        get_put_ne (by rw [← home_eq hn]; exact Ne.symm (hl2 x List.mem_cons_self)), ha1,
        get_put_ne (Ne.symm (hl1 _))]
    · intro j y hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, home_eq hn, f3 _ (fun cl he => by cases he) hdist, ha2,
          get_put_self hih (by rw [hsz1]; exact hihlt), ha1,
          get_put_self his (by rw [hsz]; exact hislt)]
      | succ j =>
        have hj' : L[j]? = some y := by simpa using hj
        rw [show s + (j + 1) = s + 1 + j by omega, f4 j y hj', ha2,
          get_put_ne (by intro he; injection he with h1; omega), ha1,
          get_put_ne (by intro he; cases he)]

end


/-- The actual indexed parallel copy passes the real move checker from every
correctly sized symbolic state. It gives every distinct destination the old
source content (including cycles), and frames all other homes/save locations.
Vector/class/parameter properties are internal VCode facts, to be derived from
the original source pipeline when composing universal fallback acceptance. -/
theorem spillArgMovesAt_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (hsl : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {b j target : Nat} {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args) (atTarget : vc.blocks[target]? = some tb)
    (size : args.size = tb.params.size)
    (classes : ∀ (i : Nat) (a p : Reg),args[i]? = some a → tb.params[i]? = some p →
      ∃ v w cl,a = .vreg v cl ∧ p = .vreg w cl)
    (distinct : (tb.params.toList.map Reg.homeNum).Nodup)
    {k : Nat} (beforeTerminator : k ≠ vb.insts.size) {a0 : AState} (stateSize : a0.size = stateSizeAt vc edges) :
    Runs c vb k (spillArgMovesAt (spillHomesAt vc edges) args tb.params) a0 fun k' a' =>
      k' = k ∧ a'.size = stateSizeAt vc edges ∧
      (∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
        a'.get (spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) =
          a0.get (spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls)) ∧
      ∀ l,(∀ cl,l ≠ .reg (spillScratch cl)) →
        (∀ i cl,l ≠ .stack ((spillHomesAt vc edges).size+i) cl) →
        (∀ p ∈ tb.params.toList,l ≠ spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) →
        a'.get l = a0.get l := by
  let pairs := args.toList.zip tb.params.toList
  have pairAt {x : Reg × Reg} (inside : x ∈ pairs) :
      ∃ (i : Nat),args[i]? = some x.1 ∧ tb.params[i]? = some x.2 := by
    obtain ⟨i,bound,equal⟩ := List.getElem_of_mem inside
    have atIndex : pairs[i]? = some x := by rw [List.getElem?_eq_getElem bound,equal]
    obtain ⟨left,right⟩ := List.getElem?_zip_eq_some.mp atIndex
    exact ⟨i,by simpa only [Array.getElem?_toList] using left,by simpa only [Array.getElem?_toList] using right⟩
  have argsHomes : ∀ x ∈ pairs,∃ n,homeLookup (spillHomesAt vc edges)
      (spillHomeKeyAt x.1.homeNum x.1.homeCls) = some n := by
    intro x inside
    obtain ⟨i,left,right⟩ := pairAt inside
    exact (spillHomesAt_spec vc edges).outgoing b j i row args x.1 atRow atArgs left
  have paramsHomes : ∀ x ∈ pairs,∃ n,homeLookup (spillHomesAt vc edges)
      (spillHomeKeyAt x.2.homeNum x.2.homeCls) = some n := by
    intro x inside
    obtain ⟨i,left,right⟩ := pairAt inside
    obtain ⟨v,w,cl,ar,param⟩ := classes i x.1 x.2 left right
    have member : (w,cl) ∈ blockVregs tb := by
      apply List.mem_append_left
      apply List.mem_filterMap.mpr
      exact ⟨x.2,List.mem_append_left _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? right)),by rw [param]⟩
    simpa only [param,Reg.homeNum,Reg.homeCls] using (spillHomesAt_spec vc edges).code target tb atTarget (w,cl) member
  have length : pairs.length ≤ maxArgsAt edges := by
    have bound := (spillAllocAt_storage vc edges).2.2 b j row args atRow atArgs
    simpa only [pairs,List.length_zip,Array.length_toList,size,Nat.min_self] using bound
  have mapped : pairs.map (·.2.homeNum) = tb.params.toList.map Reg.homeNum := by
    rw [show (fun x : Reg × Reg => x.2.homeNum) = Reg.homeNum ∘ Prod.snd from rfl,← List.map_map]
    dsimp only [pairs]
    rw [List.map_snd_zip (by simp [size])]
  rw [copy_eq]
  refine Runs.append (phase1_runs hsl beforeTerminator pairs 0 a0 argsHomes (by omega) stateSize)
    fun k1 a1 ⟨same,size1,frame1,values1⟩ => ?_
  subst k1
  refine (phase2_runs hsl beforeTerminator pairs 0 a1 paramsHomes (by rw [mapped];exact distinct) (by omega) size1).mono
    fun k2 a2 ⟨same,size2,frame2,values2⟩ => ⟨same,size2,?_,?_⟩
  · intro i ar p atAr atP
    have zipped : pairs[i]? = some (ar,p) := List.getElem?_zip_eq_some.mpr
      ⟨by simpa only [Array.getElem?_toList] using atAr,by simpa only [Array.getElem?_toList] using atP⟩
    obtain ⟨v,w,cl,rfl,rfl⟩ := classes i ar p atAr atP
    have first := values1 i _ zipped
    have second := values2 i _ zipped
    simp only [Nat.zero_add,Reg.homeNum,Reg.homeCls] at first second ⊢
    rw [second,first]
  · intro l scratch temp dest
    rw [frame2 l scratch (fun x inside => dest x.2 (List.of_mem_zip inside).2),
      frame1 l scratch (fun i cl _ => temp i cl)]

end Backend.Proof.PerEdgeSpill

