import FV.Opt.MidValCert
import FV.Opt.Proof.DomInv

/-!
# Terms of the mid-end validator: their values (#1119, module (4))

The certificate of `Opt.MidVal.checkCert` (`FV/Opt/MidValCert.lean`) names every value of `f`
and `g` by a term of its table. Here terms get values in a frame `fr` of `f`:

* an atom stands for a value of `f` (`atomVal`: `param b i` the parameter `i` of block `b`,
  `res b k j` result `j` of statement `k` of block `b`, `poison b k` the result of a removed
  `notrap` load) and reads `fr`'s register;
* a node is `evalNode` of its instruction in `fr` with the registers replaced by the values of
  earlier terms (`tmVal`, well-founded on the term id).

Facts proved: the dominance order of sites (`LeP`, `CC.le_sound`, `LeP.trans`, `avail_of_leP`);
a term whose site is no later than a point has the same value in two frames that agree on the
values available there (`tmVal_congr`): this is why values computed earlier stay valid; a node
term built from operands' terms has the value of the instruction it names (`tmVal_mapOperands`,
`tmVal_mapOperands_inst` for any instruction); and the normaliser seam `NormSound` with its
identity instance `normSound_id`, its typed form `NormSoundT f` (equality in the frames where
the atoms below the node hold values of their static types, `AtomsTyped`; `NormSound.toT`), and
`NormSoundD f` (where moreover the node's operands have values; `NormSoundT.toD`).
-/

namespace Opt.MidVal

open Clif

/-! ## The dominance order on program points -/

/-- `a ≤ b` in the dominance order of `idom` (`CC.le` as a proposition): the same block and
an earlier position, or a strict tree ancestor. -/
def LeP (idom : Array (Option Nat)) (a b : Nat × Nat) : Prop :=
  (a.1 = b.1 ∧ a.2 ≤ b.2) ∨ (a.1 ≠ b.1 ∧ Anc idom a.1 b.1)

theorem CC.le_sound {c : CC} {a b : Nat × Nat} (h : c.le a b = true) : LeP c.idom a b := by
  obtain ⟨d, t⟩ := a
  obtain ⟨i, k⟩ := b
  simp only [CC.le] at h
  by_cases hd : d = i
  · subst hd
    simp only [beq_self_eq_true, ite_true, decide_eq_true_eq] at h
    exact .inl ⟨rfl, h⟩
  · have hb : (d == i) = false := by simpa using hd
    rw [hb] at h
    exact .inr ⟨hd, ancB_sound h⟩

theorem LeP.refl (idom : Array (Option Nat)) (a : Nat × Nat) : LeP idom a a :=
  .inl ⟨rfl, Nat.le_refl _⟩

theorem LeP.trans {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) {a b c : Nat × Nat}
    (h1 : LeP idom a b) (h2 : LeP idom b c) : LeP idom a c := by
  rcases h1 with ⟨e1, l1⟩ | ⟨n1, a1⟩ <;> rcases h2 with ⟨e2, l2⟩ | ⟨n2, a2⟩
  · exact .inl ⟨e1.trans e2, Nat.le_trans l1 l2⟩
  · exact .inr ⟨by rw [e1]; exact n2, by rw [e1]; exact a2⟩
  · exact .inr ⟨by rw [← e2]; exact n1, by rw [← e2]; exact a1⟩
  · by_cases h : a.1 = c.1
    · rw [h] at a1 n1
      exact absurd (Anc.antisymm hr a2 a1) (Ne.symm n1)
    · exact .inr ⟨h, a1.trans a2⟩

/-- A later position of the same block. -/
theorem LeP.mono {idom : Array (Option Nat)} {a : Nat × Nat} {i k k' : Nat} (h : LeP idom a (i, k))
    (hk : k ≤ k') : LeP idom a (i, k') := by
  rcases h with ⟨e, l⟩ | ⟨n, an⟩
  · exact .inl ⟨e, Nat.le_trans l hk⟩
  · exact .inr ⟨n, an⟩

/-- A point of a strict tree ancestor of `i` precedes every point of `i`. -/
theorem LeP.of_anc {idom : Array (Option Nat)} {a : Nat × Nat} {i : Nat} (hne : a.1 ≠ i)
    (h : Anc idom a.1 i) (k : Nat) : LeP idom a (i, k) :=
  .inr ⟨hne, h⟩

theorem avail_of_leP {W : WfData} {v : ValueId} {s : Nat × Nat} (hd : W.dm v = some s) {i k : Nat}
    (h : LeP W.idom s (i, k)) : Avail W i k v := by
  obtain ⟨d, t⟩ := s
  exact ⟨d, t, hd, h⟩

theorem leP_of_avail {W : WfData} {v : ValueId} {i k : Nat} (h : Avail W i k v) :
    ∃ s, W.dm v = some s ∧ LeP W.idom s (i, k) := by
  obtain ⟨d, t, hd, h⟩ := h
  exact ⟨(d, t), hd, h⟩

/-! ## Atoms -/

/-- The value of `f` an atom stands for (module doc). -/
def atomVal (f : Function) : Tm → Option ValueId
  | .param b i => (f.blocks[b]?).bind fun blk => (blk.params[i]?).map (·.1)
  | .res b k j => (f.blocks[b]?).bind fun blk => (blk.body[k]?).bind fun st => st.results[j]?
  | .poison b k => (f.blocks[b]?).bind fun blk => (blk.body[k]?).bind fun st => st.results[0]?
  | .node _ => none

/-- The definition site of an atom (`CC.tmOk` checks it is the term's site). -/
def Tm.site? : Tm → Option (Nat × Nat)
  | .param b _ => some (b, 0)
  | .res b k _ => some (b, k + 1)
  | .poison b k => some (b, k + 1)
  | .node _ => none

theorem atomVal_defSite {f : Function} {a : Tm} {v : ValueId} (h : atomVal f a = some v) :
    ∃ s, a.site? = some s ∧ (v, s) ∈ defSites f := by
  cases a with
  | param b i =>
    simp only [atomVal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨blk, hb, p, hp, rfl⟩ := h
    exact ⟨(b, 0), rfl, mem_defSites.2 ⟨b, blk, hb, .inl ⟨p, List.mem_of_getElem? hp, rfl, rfl⟩⟩⟩
  | res b k j =>
    simp only [atomVal, Option.bind_eq_some_iff] at h
    obtain ⟨blk, hb, st, hst, hr⟩ := h
    exact ⟨(b, k + 1), rfl, mem_defSites.2 ⟨b, blk, hb, .inr ⟨k, st, hst, List.mem_of_getElem? hr, rfl⟩⟩⟩
  | poison b k =>
    simp only [atomVal, Option.bind_eq_some_iff] at h
    obtain ⟨blk, hb, st, hst, hr⟩ := h
    exact ⟨(b, k + 1), rfl, mem_defSites.2 ⟨b, blk, hb, .inr ⟨k, st, hst, List.mem_of_getElem? hr, rfl⟩⟩⟩
  | node _ => cases h

theorem CC.tmOk_atom {c : CC} {t : Nat} {a : Tm} {s : Nat × Nat} (h : c.tmOk t a = true)
    (hs : a.site? = some s) : c.siteOf t = s := by
  cases a with
  | node _ => cases hs
  | param b i =>
    simp only [Tm.site?, Option.some.injEq] at hs
    subst hs
    simpa [CC.tmOk] using h
  | res b k j =>
    simp only [Tm.site?, Option.some.injEq] at hs
    subst hs
    simpa [CC.tmOk] using h
  | poison b k =>
    simp only [Tm.site?, Option.some.injEq] at hs
    subst hs
    simpa [CC.tmOk] using h

theorem CC.tmOk_node {c : CC} {t : Nat} {i : Inst} (h : c.tmOk t (.node i) = true) :
    ∀ o ∈ operands i, o < t ∧ c.le (c.siteOf o) (c.siteOf t) = true := by
  intro o ho
  simp only [CC.tmOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h o ho

theorem CC.tmsOk_get {c : CC} (h : c.tmsOk = true) {t : Nat} {x : Tm} (hx : c.cert.tms[t]? = some x) :
    c.tmOk t x = true := by
  simp only [CC.tmsOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 (x, t) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hx))

/-! ## Values of terms -/

/-- The value of term `t` of the table `tms` in the frame `fr` of `f` (module doc). -/
def tmVal (f : Function) (tms : Array Tm) (fr : Frame) (mem : Mem) (t : Nat) : Option Val :=
  match tms[t]? with
  | some (.node i) =>
    evalNode { fr with regs := fun o => if _h : o < t then tmVal f tms fr mem o else none } mem i
  | some a => (atomVal f a).bind fr.regs
  | none => none
termination_by t

theorem tmVal_eq (f : Function) (tms : Array Tm) (fr : Frame) (mem : Mem) (t : Nat) :
    tmVal f tms fr mem t = match tms[t]? with
      | some (.node i) =>
        evalNode { fr with regs := fun o => if _h : o < t then tmVal f tms fr mem o else none } mem i
      | some a => (atomVal f a).bind fr.regs
      | none => none := by
  rw [tmVal]

/-- The frame in which node terms are evaluated: `fr` with every term's value as register. -/
def tmFrame (f : Function) (tms : Array Tm) (fr : Frame) (mem : Mem) : Frame :=
  { fr with regs := fun o => tmVal f tms fr mem o }

theorem tmVal_atom {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t : Nat} {a : Tm}
    (h : tms[t]? = some a) (ha : ∀ i, a ≠ .node i) : tmVal f tms fr mem t = (atomVal f a).bind fr.regs := by
  rw [tmVal_eq, h]
  cases a with
  | node i => exact absurd rfl (ha i)
  | _ => rfl

theorem tmVal_node {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t : Nat} {i : Inst}
    (h : tms[t]? = some (.node i)) (hlt : ∀ o ∈ operands i, o < t) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i := by
  rw [tmVal_eq, h]
  exact evalNode_congr rfl rfl rfl fun o ho => by simp [tmFrame, hlt o ho]

/-- A node built from the operands' terms (`mapOperands σ`) has the value of the instruction
in any frame `fr0` of the same globals, externs and slots whose registers hold the operands'
term values. -/
theorem tmVal_mapOperands {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t : Nat}
    {σ : ValueId → Nat} {i : Inst} {fr0 : Frame} (h : tms[t]? = some (.node (mapOperands σ i)))
    (hlt : ∀ x ∈ operands i, σ x < t)
    (hg : fr.func.globals = fr0.func.globals) (hx : fr.func.externs = fr0.func.externs)
    (hs : fr.slots = fr0.slots)
    (hr : ∀ x ∈ operands i, tmVal f tms fr mem (σ x) = fr0.regs x) :
    tmVal f tms fr mem t = evalNode fr0 mem i := by
  rw [tmVal_node h (by
    intro o ho
    rw [operands_mapOperands, List.mem_map] at ho
    obtain ⟨x, hx, rfl⟩ := ho
    exact hlt x hx)]
  exact evalNode_rename hg hx hs hr

/-- The same for any instruction (no single-result requirement): its evaluation in the term
frame, renamed, equals its evaluation in `fr0` up to `stuck` messages. -/
theorem tmVal_mapOperands_inst {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem}
    {σ : ValueId → Nat} {i : Inst} {fr0 : Frame}
    (hg : fr.func.globals = fr0.func.globals) (hx : fr.func.externs = fr0.func.externs)
    (hs : fr.slots = fr0.slots)
    (hr : ∀ x ∈ operands i, tmVal f tms fr mem (σ x) = fr0.regs x) :
    (evalInst (tmFrame f tms fr mem) mem (mapOperands σ i)).norm = (evalInst fr0 mem i).norm :=
  evalInst_rename hg hx hs hr

/-- **Stability.** In two frames with the same globals, externs and slots that agree on every
value of `f` available at `(i, k)`, every term whose site is no later than `(i, k)` has the same
value (atoms of such a term are available there). From the two facts of `Opt.Wf` it reads (the
tree's rank and the definition sites), so that `Opt.Wf` and `WfM` both give it. -/
theorem tmVal_congr_of {f : Function} {W : WfData}
    (hrank : ∀ b c, W.idom[b]?.join = some c → W.rank c < W.rank b)
    (hsites : ∀ v s, (v, s) ∈ defSites f → W.dm v = some s) {c : CC} (hidom : c.idom = W.idom)
    (hok : c.tmsOk = true) {fr1 fr2 : Frame} {mem : Mem}
    (hg : fr2.func.globals = fr1.func.globals) (hx : fr2.func.externs = fr1.func.externs)
    (hs : fr2.slots = fr1.slots) {i k : Nat} (hr : ∀ v, Avail W i k v → fr2.regs v = fr1.regs v) :
    ∀ t, LeP W.idom (c.siteOf t) (i, k) →
      tmVal f c.cert.tms fr2 mem t = tmVal f c.cert.tms fr1 mem t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro hle
    rw [tmVal_eq f _ fr2, tmVal_eq f _ fr1]
    cases ht : c.cert.tms[t]? with
    | none => rfl
    | some x =>
      have hx' := CC.tmsOk_get hok ht
      cases x with
      | node n =>
        simp only
        refine evalNode_congr hg hx hs fun o ho => ?_
        obtain ⟨hlt, hle'⟩ := CC.tmOk_node hx' o ho
        have hle'' := CC.le_sound hle'
        rw [hidom] at hle''
        simp only [hlt, dite_true]
        exact ih o hlt (hle''.trans hrank hle)
      | _ =>
        simp only
        cases hv : atomVal f _ with
        | none => rfl
        | some v =>
          obtain ⟨s, hs', hd⟩ := atomVal_defSite hv
          have hst := CC.tmOk_atom hx' hs'
          rw [hst] at hle
          simp only [Option.bind_some]
          exact hr v (avail_of_leP (hsites v s hd) hle)

/-- **Stability** (`tmVal_congr_of`) for a function with the facts `Opt.Wf`. -/
theorem tmVal_congr {f : Function} {W : WfData} (hW : Wf f W) {c : CC} (hidom : c.idom = W.idom)
    (hok : c.tmsOk = true) {fr1 fr2 : Frame} {mem : Mem}
    (hg : fr2.func.globals = fr1.func.globals) (hx : fr2.func.externs = fr1.func.externs)
    (hs : fr2.slots = fr1.slots) {i k : Nat} (hr : ∀ v, Avail W i k v → fr2.regs v = fr1.regs v) :
    ∀ t, LeP W.idom (c.siteOf t) (i, k) →
      tmVal f c.cert.tms fr2 mem t = tmVal f c.cert.tms fr1 mem t :=
  tmVal_congr_of hW.rank hW.sites hidom hok hg hx hs hr

/-! ## The normaliser seam -/

/-- A normaliser is sound when the term it gives for a node has, in every frame, the value of
the node evaluated on the terms' values (`tmFrame`). -/
def NormSound (norm : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), norm tms i = some x →
    ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

/-- Stage 1: the identity normaliser (`Norm.id`, no rewrite) is sound. -/
theorem normSound_id : NormSound Norm.id := by
  intro _ _ _ h
  cases h

/-! ## The typed normaliser seam -/

/-- Term `u` is reachable from the operands of `i` through node operands. -/
inductive TmReach (tms : Array Tm) (i : Inst) : Nat → Prop
  | op {u : Nat} : u ∈ operands i → TmReach tms i u
  | sub {w u : Nat} {j : Inst} : TmReach tms i w → tms[w]? = some (.node j) → u ∈ operands j →
      TmReach tms i u

/-- The atoms reachable from the operands of `i` that have a static type in `f` (`atomTy`) hold
values of that type in the frame `fr`. -/
def AtomsTyped (f : Function) (tms : Array Tm) (fr : Frame) (mem : Mem) (i : Inst) : Prop :=
  ∀ (u : Nat) (a : Tm) (ty : Ty) (v : Val), TmReach tms i u → tms[u]? = some a →
    atomTy f a = some ty → tmVal f tms fr mem u = some v → v.ty = ty

/-- A normaliser is sound for `f` under typing when the term it gives for a node has the node's
value in every frame of `f` where the atoms below the node are typed (`AtomsTyped`). -/
def NormSoundT (f : Function) (norm : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), norm tms i = some x →
    ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x → AtomsTyped f tms fr mem i →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

/-- A normaliser sound in every frame is sound under typing. -/
theorem NormSound.toT {norm : Norm} {f : Function} (h : NormSound norm) : NormSoundT f norm :=
  fun tms i x hx fr mem t ht _ => h tms i x hx f fr mem t ht

/-! ## The normaliser seam with defined operands -/

/-- A normaliser is sound for `f` where the operands have values when the term it gives for a
node has the node's value in every frame of `f` where the atoms below the node are typed
(`AtomsTyped`) and the node's operands have values. Rules that drop an operand (`(x + y) - x =
y`, `x * 0 = 0`) meet it and not `NormSoundT`; the simulation evaluates a node only where its
operands, the terms of available values, have values. -/
def NormSoundD (f : Function) (norm : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), norm tms i = some x →
    ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x → AtomsTyped f tms fr mem i →
      (∀ o ∈ operands i, (tmVal f tms fr mem o).isSome) →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

/-- A normaliser sound under typing is sound where the operands have values. -/
theorem NormSoundT.toD {norm : Norm} {f : Function} (h : NormSoundT f norm) : NormSoundD f norm :=
  fun tms i x hx fr mem t ht hA _ => h tms i x hx fr mem t ht hA

end Opt.MidVal
