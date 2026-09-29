import FV.Opt.Check
import FV.Opt.Proof.SemSim

/-!
# Dominance: what `Opt.check` guarantees (`wfCert`), declaratively

`Opt.Wf f W` collects the facts of the certificate `Opt.wfCert` (checked by `Opt.check`) about
a function `f`, relative to its data `W` (dominator tree `idom`, definition sites `dm`, types
`tm`, block index `index`). `Opt.wf_of_check` derives it from a successful `check`.

The key notion is `Opt.Avail W i k v`: `v` is available before statement `k` of block `i`
(its definition is earlier in the block, or in a strict tree ancestor). The edge certificate
makes the values available at the start of a block (other than its parameters) available at
the end of every predecessor — this is the dominance lemma (D) of `docs/contracts/midend.md` in
the form the simulations use (`FV/Opt/Proof/DomInv.lean`).
-/

namespace Opt

open Clif

/-! ## The dominator tree -/

/-- Tree ancestor (reflexive). -/
inductive Anc (idom : Array (Option Nat)) : Nat → Nat → Prop
  | refl (a : Nat) : Anc idom a a
  | up {a b c : Nat} : idom[b]?.join = some c → Anc idom a c → Anc idom a b

theorem ancB_sound {idom : Array (Option Nat)} :
    ∀ {fuel a b}, ancB idom fuel a b = true → Anc idom a b := by
  intro fuel
  induction fuel with
  | zero => intro a b h; simp only [ancB, beq_iff_eq] at h; subst h; exact .refl _
  | succ n ih =>
    intro a b h
    simp only [ancB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl _
    · split at h
      · exact .up ‹_› (ih h)
      · cases h

theorem Anc.trans {idom : Array (Option Nat)} {a b c : Nat} (h1 : Anc idom a b)
    (h2 : Anc idom b c) : Anc idom a c := by
  induction h2 with
  | refl => exact h1
  | up hc _ ih => exact .up hc ih

theorem Anc.rank_le {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) {a b : Nat} (h : Anc idom a b) :
    rank a ≤ rank b ∧ (a ≠ b → rank a < rank b) := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩
  | up hc _ ih =>
    have := hr _ _ hc
    exact ⟨by omega, fun _ => by omega⟩

theorem Anc.antisymm {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) {a b : Nat} (h1 : Anc idom a b)
    (h2 : Anc idom b a) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  have := (h1.rank_le hr).2 hne
  have := (h2.rank_le hr).1
  omega

/-- A strict ancestor of `b` is an ancestor of `idom b`. -/
theorem Anc.strict {idom : Array (Option Nat)} {a b : Nat} (h : Anc idom a b) (hne : a ≠ b) :
    ∃ c, idom[b]?.join = some c ∧ Anc idom a c := by
  cases h with
  | refl => exact absurd rfl hne
  | up hc h => exact ⟨_, hc, h⟩

/-! ## Certificate data -/

/-- The data a certificate is relative to. -/
structure WfData where
  idom : Array (Option Nat)
  rank : Nat → Nat
  dm : ValueId → Option (Nat × Nat)
  tm : ValueId → Option Ty
  index : BlockId → Option Nat

/-- `v` is available before statement `k` of block `i`. -/
def Avail (W : WfData) (i k : Nat) (v : ValueId) : Prop :=
  ∃ d t, W.dm v = some (d, t) ∧ ((d = i ∧ t ≤ k) ∨ (d ≠ i ∧ Anc W.idom d i))

/-- `sigOf` of `Opt.check`. -/
def sigOf (f : Function) (r : FnRef) : Option Signature := (f.externs.lookup r).map (·.sig)

/-- The facts of `wfCert`. -/
structure Wf (f : Function) (W : WfData) : Prop where
  ids : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → W.index b.id = some i
  sites : ∀ v s, (v, s) ∈ defSites f → W.dm v = some s
  sitesRev : ∀ v s, W.dm v = some s → (v, s) ∈ defSites f
  root : W.idom[0]?.join = none
  rank : ∀ b c, W.idom[b]?.join = some c → W.rank c < W.rank b
  params : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ p ∈ b.params, W.tm p.1 = some p.2
  uses : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    ∀ v ∈ operands st.inst, Avail W i j v
  results : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    ∃ ts, st.inst.resultTypes (sigOf f) (fun _ => none) = some ts ∧ ts.length = st.results.length ∧
      ∀ (n : Nat) r, st.results[n]? = some r → W.tm r = ts[n]?
  pure : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ (j : Nat) (st : Stmt), b.body[j]? = some st →
    isPure st.inst = true → pureTyped W.tm f st.inst = true
  termUses : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ v ∈ termOperands b.term, Avail W i b.body.length v
  edges : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ id ∈ termSuccs b.term, ∃ j, ∃ b' : Block, W.index id = some j ∧
    f.blocks[j]? = some b' ∧ b'.id = id ∧ ∀ c, W.idom[j]?.join = some c → Anc W.idom c i

/-- The certificate data `check` uses. -/
def wfData (f : Function) (info : Info) : WfData where
  idom := info.cfg.idom
  rank b := (info.cfg.rpoNum[b]?.join).getD 0
  dm v := (defMap f).get? v
  tm v := info.types.get? v
  index id := info.cfg.index.get? id

/-! ## Soundness of `wfCert` -/

theorem mem_defSites {f : Function} {v : ValueId} {s : Nat × Nat} :
    (v, s) ∈ defSites f ↔ ∃ i b, f.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, p.1 = v ∧ s = (i, 0)) ∨
        ∃ j st, b.body[j]? = some st ∧ v ∈ st.results ∧ s = (i, j + 1)) := by
  simp only [defSites, List.mem_flatMap, List.mem_append, List.mem_map,
    List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨b, i⟩, hb, ⟨p, hp, he⟩ | ⟨⟨st, j⟩, hst, r, hr, he⟩⟩
    · simp only [Prod.mk.injEq] at he
      exact ⟨i, b, hb, .inl ⟨p, hp, he.1, he.2.symm⟩⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨i, b, hb, .inr ⟨j, st, hst, hr, rfl⟩⟩
  · rintro ⟨i, b, hb, ⟨p, hp, h1, rfl⟩ | ⟨j, st, hst, hr, rfl⟩⟩
    · exact ⟨(b, i), hb, .inl ⟨p, hp, by rw [h1]⟩⟩
    · exact ⟨(b, i), hb, .inr ⟨(st, j), hst, v, hr, rfl⟩⟩

theorem foldl_insert_get {l : List (ValueId × Nat × Nat)} :
    ∀ (m : Std.HashMap ValueId (Nat × Nat)) v s,
      (l.foldl (fun m (x : ValueId × Nat × Nat) => m.insert x.1 x.2) m).get? v = some s →
      m.get? v = some s ∨ (v, s) ∈ l := by
  induction l with
  | nil => intro m v s h; exact .inl h
  | cons x l ih =>
    intro m v s h
    rcases ih _ v s h with h | h
    · rw [Std.HashMap.get?_insert] at h
      split at h
      · rename_i he
        simp only [beq_iff_eq] at he
        cases h; subst he; exact .inr (by simp)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem availB_sound {W : WfData} {i k v}
    (h : availB W.dm (ancB W.idom W.idom.size) i k v = true) : Avail W i k v := by
  simp only [availB] at h
  split at h
  · rename_i d t hd
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      bne_iff_ne, ne_eq] at h
    refine ⟨d, t, hd, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, ancB_sound h2⟩
  · cases h

theorem wfCert_sound {f : Function} {info : Info} (h : wfCert f info.cfg info.types = true) :
    Wf f (wfData f info) := by
  simp only [wfCert, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hids, hsites⟩, hroot⟩, hrank⟩, hblocks⟩ := h
  have hmem : ∀ {α : Type} {l : List α} {i : Nat} {x : α}, l[i]? = some x → (x, i) ∈ l.zipIdx :=
    fun h => List.mem_zipIdx_iff_getElem?.2 h
  refine
    { ids := fun i b hb => by
        simpa [wfData, Std.HashMap.get?_eq_getElem?] using hids _ (hmem hb)
      sites := fun v s hs => by simpa [wfData] using hsites _ hs
      sitesRev := fun v s hs => by
        rcases foldl_insert_get _ v s hs with h | h
        · simp at h
        · exact h
      root := by simpa [wfData] using hroot
      rank := fun b c hc => by
        simp only [wfData] at hc ⊢
        have hb : b < info.cfg.idom.size := by
          rcases Nat.lt_or_ge b info.cfg.idom.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hc; cases hc
        have := hrank b (List.mem_range.2 hb)
        simp only [hc] at this
        simpa [wfData] using this
      params := ?_, uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  all_goals intro i b hb
  all_goals obtain ⟨⟨⟨hpar, hbody⟩, hterm⟩, hsucc⟩ := by simpa using hblocks _ (hmem hb)
  · intro p hp; simpa [wfData, Std.HashMap.get?_eq_getElem?] using hpar p.1 p.2 hp
  · intro j st hst v hv
    exact availB_sound (by simpa [wfData] using (hbody st j (hmem hst)).1.1 v hv)
  · intro j st hst
    have h2 := (hbody st j (hmem hst)).1.2
    split at h2
    · rename_i ts hts
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
      refine ⟨ts, hts, h2.1, fun n r hr => ?_⟩
      have hn : n < ts.length := by
        rw [h2.1]; exact (List.getElem?_eq_some_iff.1 hr).1
      have hz : (r, ts[n]) ∈ st.results.zip ts :=
        List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hr]⟩
      have := h2.2 _ hz
      simpa [wfData, List.getElem?_eq_getElem hn] using this
    · cases h2
  · intro j st hst hp
    have h3 := (hbody st j (hmem hst)).2
    simpa [hp, wfData, Std.HashMap.get?_eq_getElem?] using h3
  · intro v hv
    exact availB_sound (by simpa [wfData] using hterm v hv)
  · intro id hid
    have h4 := hsucc id hid
    split at h4
    · rename_i j hj
      simp only [Bool.and_eq_true, beq_iff_eq] at h4
      obtain ⟨h5, h6⟩ := h4
      cases hbj : f.blocks[j]? with
      | none => simp [hbj] at h5
      | some b' =>
        simp only [hbj, Option.map_some, Option.some.injEq] at h5
        refine ⟨j, b', hj, hbj, h5, fun c hc => ?_⟩
        simp only [wfData] at hc
        simp only [hc] at h6
        exact ancB_sound h6
    · cases h4

/-- `check` establishes the certificate facts. -/
theorem wf_of_check {f : Function} {info : Info} (h : check f = .ok info) : Wf f (wfData f info) := by
  have : wfCert f info.cfg info.types = true := by
    unfold check at h
    cases hc : checkCore f with
    | error e => simp [hc, bind, Except.bind] at h
    | ok i =>
      simp only [hc, bind, Except.bind, ensure, pure, Except.pure] at h
      by_cases hw : wfCert f i.cfg i.types = true
      · simp only [hw, ite_true] at h; cases h; exact hw
      · simp only [hw] at h; cases h
  exact wfCert_sound this

end Opt
