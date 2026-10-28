import FV.Backend.Proof.CleanupStageSpill
import FV.Backend.Proof.DropSublist
import FV.Backend.Proof.DeadCleanupPreparedAvailability

/-!
# Spill availability through the skip of unused instructions

The skip (`skipStage`) deletes, in the prepared code, only instructions whose defs are dead
(`deadDefs`): no kept instruction and no branch argument reads them. Restricting the
availability sets to the other vregs, availability of every such vreg is unchanged by the
deletion, so the availability facts (`SpillAvail`) transport (`skipPrepared_spillAvail`).
-/

namespace Backend.Proof.Driver
open Backend Backend.DeadCleanup Backend.Proof.Spill

section
variable (N : Nat → Bool)

/-- `A` and `B` agree off the dead vregs `N`. -/
def AgreeOff (A B : Nat → Bool) : Prop := ∀ v, N v = false → A v = B v

private theorem sa_inst (i : MInst) {A B : Nat → Bool} (h : AgreeOff N A B) :
    AgreeOff N (availInst i A) (availInst i B) := by
  intro v hv
  unfold availInst
  cases i.operands with
  | error _ => exact h v hv
  | ok ops =>
    dsimp only
    split
    · rfl
    · exact h v hv

private theorem sa_del (i : MInst) (A : Nat → Bool) (hd : ∀ d ∈ defNums i, N d = true) :
    AgreeOff N (availInst i A) A := by
  intro v hv
  unfold availInst
  cases hop : i.operands with
  | error _ => rfl
  | ok ops =>
    dsimp only
    rw [if_neg]
    intro h
    obtain ⟨o, ho, he⟩ := List.any_eq_true.mp h
    have hov : o.vreg = v := by simpa using he
    have := hd o.vreg (by simp only [defNums, hop]; exact List.mem_map.mpr ⟨o, ho, rfl⟩)
    rw [hov, hv] at this
    cases this

private theorem sa_ready (i : MInst) {A B : Nat → Bool} (h : AgreeOff N A B)
    (hu : ∀ u ∈ useNums i, N u = false) (hr : ReadsReady i A) : ReadsReady i B := by
  unfold ReadsReady at hr ⊢
  cases hop : i.operands with
  | error _ => trivial
  | ok ops =>
    simp only [hop] at hr ⊢
    intro o ho hk
    have hm : o.vreg ∈ useNums i := by
      simp only [useNums, hop]
      exact List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, by simp [hk]⟩, rfl⟩
    rw [← h _ (hu _ hm)]
    exact hr o ho hk

private theorem sa_walk : ∀ (ms : List MInst) (m : List Bool), m.length = ms.length →
    (∀ (k : Nat) (x : MInst), ms[k]? = some x → m[k]? = some false → ∀ d ∈ defNums x, N d = true) →
    (∀ (k : Nat) (x : MInst), ms[k]? = some x → m[k]? = some true → ∀ u ∈ useNums x, N u = false) →
    ∀ A B, AgreeOff N A B → AvailRunReady ms A →
      AvailRunReady (maskKeep m ms) B ∧
      AgreeOff N (ms.foldl (fun A i => availInst i A) A)
        ((maskKeep m ms).foldl (fun B i => availInst i B) B)
  | [], m, _, _, _, A, B, h, _ => by
    simp only [maskKeep, List.zip_nil_left, List.filterMap_nil, List.foldl_nil]
    exact ⟨trivial, h⟩
  | i :: ms, [], hl, _, _, _, _, _, _ => by simp at hl
  | i :: ms, k :: m, hl, hd, hu, A, B, h, hr => by
    obtain ⟨hr1, hr2⟩ := hr
    have hl' : m.length = ms.length := by simpa using hl
    have hd' : ∀ (k : Nat) (x : MInst), ms[k]? = some x → m[k]? = some false →
        ∀ d ∈ defNums x, N d = true :=
      fun k x h1 h2 => hd (k + 1) x (by simpa using h1) (by simpa using h2)
    have hu' : ∀ (k : Nat) (x : MInst), ms[k]? = some x → m[k]? = some true →
        ∀ u ∈ useNums x, N u = false :=
      fun k x h1 h2 => hu (k + 1) x (by simpa using h1) (by simpa using h2)
    cases k with
    | false =>
      have hmk : maskKeep (false :: m) (i :: ms) = maskKeep m ms := by simp [maskKeep]
      rw [hmk]
      have h2 : AgreeOff N (availInst i A) B := fun v hv =>
        (sa_del N i A (hd 0 i rfl rfl) v hv).trans (h v hv)
      simpa using sa_walk ms m hl' hd' hu' _ _ h2 hr2
    | true =>
      have hmk : maskKeep (true :: m) (i :: ms) = i :: maskKeep m ms := by simp [maskKeep]
      rw [hmk]
      obtain ⟨a, b⟩ := sa_walk ms m hl' hd' hu' _ _ (sa_inst N i h) hr2
      exact ⟨⟨sa_ready N i h (hu 0 i rfl rfl) hr1, a⟩, by simpa using b⟩

/-- A block whose image under `T` deletes only instructions writing dead vregs, and whose kept
instructions and branch arguments read none. -/
def SkipBlockOk (T : VBlock → VBlock) (vb : VBlock) : Prop :=
  ∃ m : List Bool, (T vb).insts.toList = maskKeep m vb.insts.toList ∧
    m.length = vb.insts.toList.length ∧
    (∀ (k : Nat) (x : MInst), vb.insts.toList[k]? = some x → m[k]? = some false →
      ∀ d ∈ defNums x, N d = true) ∧
    (∀ (k : Nat) (x : MInst), vb.insts.toList[k]? = some x → m[k]? = some true →
      ∀ u ∈ useNums x, N u = false) ∧
    ∀ a ∈ vb.branchArgs.toList, N a.homeNum = false

private theorem availAt_size (insts : Array MInst) (A : Nat → Bool) :
    availAt insts A insts.size = insts.toList.foldl (fun A i => availInst i A) A := by
  unfold availAt
  rw [← Array.length_toList, List.take_length]

private theorem sa_block {T : VBlock → VBlock} (hT : DelMap T) {raw : VCode}
    {D : Nat → Nat → Bool} (hav : SpillAvail raw D) {ss ps : Array (Array Nat)}
    (hc : raw.cfg = .ok (ss, ps)) {b : Nat} {vb : VBlock} (hb : raw.blocks[b]? = some vb)
    (hok : SkipBlockOk N T vb) :
    AvailRunReady (T vb).insts.toList
        (availStart (mapBlocks T raw) ss ps (fun b v => D b v && !N v) b) ∧
      AgreeOff N (availAt vb.insts (availStart raw ss ps D b) vb.insts.size)
        (availAt (T vb).insts (availStart (mapBlocks T raw) ss ps (fun b v => D b v && !N v) b)
          (T vb).insts.size) := by
  obtain ⟨m, he, hl, hd, hu, -⟩ := hok
  have hold : AvailRunReady vb.insts.toList (availStart raw ss ps D b) := by
    apply (availRunReady_iff _ _).mpr
    intro k i ops hi hops o ho hu
    rw [Array.getElem?_toList] at hi
    exact hav.uses ss ps hc b vb k i ops hb hi hops o ho hu
  have hstart : AgreeOff N (availStart raw ss ps D b)
      (availStart (mapBlocks T raw) ss ps (fun b v => D b v && !N v) b) := by
    intro v hv
    simp [availStart, hT.entryStored_eq, hv]
  have h := sa_walk N vb.insts.toList m hl hd hu _ _ hstart hold
  rw [availAt_size, availAt_size, he]
  exact h

/-- **The transport**: if every block of `raw` is `SkipBlockOk` for `T`, availability
restricted to the non-dead vregs holds of the mapped code. -/
theorem skipAvail_of {T : VBlock → VBlock} (hT : DelMap T) (raw : VCode)
    (D : Nat → Nat → Bool) (hav : SpillAvail raw D)
    (hok : ∀ (b : Nat) (vb : VBlock), raw.blocks[b]? = some vb → SkipBlockOk N T vb) :
    SpillAvail (mapBlocks T raw) (fun b v => D b v && !N v) := by
  constructor
  · intro ss ps hc b vb' k i ops hb hi hops o ho hu
    rw [hT.cfg] at hc
    rw [mapBlocks_getElem?] at hb
    obtain ⟨vb, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hr := (sa_block N hT hav hc hb0 (hok b vb hb0)).1
    exact (availRunReady_iff _ _).mp hr k i ops (by simpa using hi) hops o ho hu
  · intro ss ps hc b vb' succ s sb' hb hsucc hs hsb v hD
    rw [hT.cfg] at hc
    rw [mapBlocks_getElem?] at hb hsb
    obtain ⟨vb, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨sb, hsb0, rfl⟩ := Option.map_eq_some_iff.mp hsb
    obtain ⟨hDold, hvN⟩ : D s v = true ∧ N v = false := by
      simpa [Bool.and_eq_true] using hD
    have hold := hav.edges ss ps hc b vb succ s sb hb0 hsucc hs hsb0 v hDold
    have hok0 := hok b vb hb0
    have hA := (sa_block N hT hav hc hb0 hok0).2
    simp only [edgeAvail, hT.map.branchArgs, hT.map.params] at hold ⊢
    cases hi : (sb.params.toList.map Reg.homeNum).idxOf? v with
    | none =>
      simp only [hi] at hold ⊢
      rw [← hA v hvN]
      exact hold
    | some k =>
      simp only [hi] at hold ⊢
      cases ha : vb.branchArgs[k]? with
      | none => simp [ha] at hold
      | some a =>
        simp only [ha] at hold ⊢
        obtain ⟨-, -, -, -, -, hargs⟩ := hok0
        rw [← hA a.homeNum (hargs a (Array.mem_toList_iff.mpr (Array.mem_of_getElem? ha)))]
        exact hold

end

private theorem sa_ct {l : List Nat} {n : Nat} (h : n ∈ l) : l.contains n = true :=
  List.contains_iff_mem.mpr h

private theorem sa_cf {l : List Nat} {n : Nat} (h : n ∉ l) : l.contains n = false :=
  Bool.eq_false_iff.mpr fun h' => h (List.contains_iff_mem.mp h')

/-- What the checked skip does to a prepared block: it deletes, in order, only `skipDel`
instructions writing dead vregs; kept instructions read no dead vreg; with the classes facts,
neither do branch arguments. -/
def PrepSkip (vc : VCode) (mask : Nat → List Bool) (vb : VBlock) : Prop :=
  ∃ m : List Bool, (skipBlock mask vb).insts.toList = maskKeep m vb.insts.toList ∧
    m.length = vb.insts.toList.length ∧
    (∀ (k : Nat) (x : MInst), vb.insts.toList[k]? = some x → m[k]? = some false →
      ∀ d ∈ defNums x, (deadDefs vc mask).contains d = true) ∧
    (∀ (k : Nat) (x : MInst), vb.insts.toList[k]? = some x → m[k]? = some true →
      ∀ u ∈ useNums x, (deadDefs vc mask).contains u = false) ∧
    (∀ (k : Nat) (x : MInst), vb.insts.toList[k]? = some x → m[k]? = some false →
      skipDel x = true) ∧
    (ClassesOkM vc → ∀ a ∈ vb.branchArgs.toList, (deadDefs vc mask).contains a.homeNum = false)

theorem PrepSkip.blockOk {vc : VCode} {mask : Nat → List Bool} {vb : VBlock}
    (h : PrepSkip vc mask vb) (hcls : ClassesOkM vc) :
    SkipBlockOk (fun v => (deadDefs vc mask).contains v) (skipBlock mask) vb := by
  obtain ⟨m, h1, h2, h3, h4, -, h6⟩ := h
  exact ⟨m, h1, h2, h3, h4, h6 hcls⟩

theorem maskKeep_drop {p : MInst → Bool} : ∀ (ms : List MInst) (m : List Bool),
    m.length = ms.length →
    (∀ (k : Nat) (x : MInst), ms[k]? = some x → m[k]? = some false → p x = true) →
    DropSublist p (maskKeep m ms) ms
  | [], _, _, _ => by simpa [maskKeep] using DropSublist.nil
  | _ :: _, [], hl, _ => by simp at hl
  | i :: ms, k :: m, hl, hp => by
    have ih := maskKeep_drop ms m (by simpa using hl)
      fun k x h1 h2 => hp (k + 1) x (by simpa using h1) (by simpa using h2)
    cases k with
    | false =>
      have hmk : maskKeep (false :: m) (i :: ms) = maskKeep m ms := by simp [maskKeep]
      rw [hmk]
      exact .drop (hp 0 i rfl rfl) ih
    | true =>
      have hmk : maskKeep (true :: m) (i :: ms) = i :: maskKeep m ms := by simp [maskKeep]
      rw [hmk]
      exact .keep ih

/-- A block of `vc` (or its retargeted copy: same operands position by position, and the same
instruction except at the last position) is `PrepSkip` for the checked mask. -/
private theorem sa_orig {vc : VCode} {mask : Nat → List Bool}
    (hchk : deleteCheck vc mask = true) {b : Nat} {ovb nb : VBlock}
    (hov : vc.blocks[b]? = some ovb) (hlab : nb.label = b)
    (hargs : nb.branchArgs = ovb.branchArgs) (hsize : nb.insts.size = ovb.insts.size)
    (hrel : ∀ (k : Nat) (x : MInst), nb.insts.toList[k]? = some x →
      ∃ y, ovb.insts.toList[k]? = some y ∧ y.operands = x.operands ∧
        (y = x ∨ k + 1 = ovb.insts.size)) :
    PrepSkip vc mask nb := by
  have hdel := deletes_of_check hchk
  have hmem : ovb ∈ vc.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hov)
  have hA : ClassesOkM vc →
      ∀ a ∈ nb.branchArgs.toList, (deadDefs vc mask).contains a.homeNum = false := by
    intro hcls a ha
    rw [hargs] at ha
    obtain ⟨n, c, rfl, _⟩ := hcls.2 ovb hmem a (List.mem_append_right _ ha)
    exact sa_cf (hdel.args b ovb _ n hov ha rfl)
  rcases hdel.last b ovb hov with h0 | hlast
  · have hnil : nb.insts.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [hsize, h0]
    refine ⟨[], ?_, by simp [hnil], by simp [hnil], by simp [hnil], by simp [hnil], hA⟩
    unfold skipBlock
    split <;> simp [hnil, maskKeep]
  · have hlen := hdel.len b ovb hov
    have hfit : MaskFits (mask b) nb.insts.toList :=
      ⟨by simp [hsize, hlen], hlast⟩
    refine ⟨mask b, ?_, hfit.1, ?_, ?_, ?_, hA⟩
    · unfold skipBlock
      rw [hlab, if_pos hfit]
    · intro k x hx hm d hdx
      obtain ⟨y, hy, hop, -⟩ := hrel k x hx
      have hdy : d ∈ vdefs y := by
        rw [← defNums_eq]; simpa only [defNums, hop] using hdx
      exact sa_ct (deadDef_of hov (by simpa using hy) hm hdy)
    · intro k x hx hm u hux
      obtain ⟨y, hy, hop, -⟩ := hrel k x hx
      have huy : u ∈ vuseNums y := by
        rw [← useNums_eq]; simpa only [useNums, hop] using hux
      exact sa_cf (hdel.uses b ovb k y hov (by simpa using hy) hm u huy)
    · intro k x hx hm
      obtain ⟨y, hy, -, hyx⟩ := hrel k x hx
      rcases hyx with rfl | hk
      · exact skipDel_of_check hchk hov (by simpa using hy) hm
      · have hl2 : (mask b)[k]? = some true := by
          rw [List.getLast?_eq_getElem?] at hlast
          rw [show k = (mask b).length - 1 by omega]
          exact hlast
        rw [hl2] at hm
        cases hm

/-- **Every prepared block is `SkipBlockOk`** for a checked mask, on code whose labels are the
block indices: a kept block is a block of `vc` or its retargeted copy; an edge block is a single
`jump`, which `skipBlock` keeps. -/
theorem prepSkip_prepare {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) {mask : Nat → List Bool}
    (hlab : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l)
    (hchk : deleteCheck vc mask = true) :
    ∀ vb ∈ raw.blocks.toList, PrepSkip vc mask vb := by
  intro vb hvb
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ :=
    Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨_, _, _, _, _, hR, _, _, _, _⟩ := Prep.facts_basic hd cs0 cs2 hS
  rw [Array.mem_toList_iff, Array.mem_map] at hvb
  obtain ⟨i, hiR, rfl⟩ := hvb
  have hi2 : i < (B ++ E).size := hR i (by simpa using hiR)
  rw [getElem!_pos (B ++ E) i hi2]
  by_cases hiB : i < B.size
  · rw [Array.getElem_append_left hiB]
    have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by
      rw [← hS.size]
      exact hiB
    obtain ⟨b, hb, e, _⟩ := Prep.keep_src hi1
    have hrw := hS.rw i hi1 hiB
    rw [e] at hrw
    have hov : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hb
    have hl := hlab b _ hov
    generalize vc.blocks[b] = ovb at hov hl hrw
    generalize B[i] = nb at hrw ⊢
    rcases hrw with rfl | ⟨t, t', ls, h1, -, h3, rfl, -⟩
    · exact sa_orig hchk hov hl rfl rfl fun k x hx => ⟨x, hx, rfl, .inl rfl⟩
    · have hne : ovb.insts.toList ≠ [] := by
        intro h0
        rw [← Array.getLast?_toList, h0] at h1
        simp at h1
      obtain ⟨ms', t0, hx⟩ := exists_append_last hne
      have ht0 : t0 = t := by
        rw [← Array.getLast?_toList, hx] at h1
        simpa using h1
      subst ht0
      have hpp : (ovb.insts.pop.push t').toList = ms' ++ [t'] := by
        simp [Array.toList_pop, hx]
      refine sa_orig hchk hov hl rfl ?_ ?_
      · have := congrArg List.length hpp
        have h2 := congrArg List.length hx
        simp only [Array.length_toList, List.length_append] at this h2
        simp only [this, h2, List.length_singleton]
      · intro k x hxk
        simp only [hpp] at hxk
        rw [hx]
        rcases Nat.lt_or_ge k ms'.length with hk | hk
        · rw [List.getElem?_append_left hk] at hxk ⊢
          exact ⟨x, hxk, rfl, .inl rfl⟩
        · rw [List.getElem?_append_right hk] at hxk ⊢
          cases hkk : k - ms'.length with
          | zero =>
            rw [hkk] at hxk
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hxk
            subst hxk
            refine ⟨t0, rfl, (setTargets_facts h3).1.symm, .inr ?_⟩
            have h2 := congrArg List.length hx
            simp only [Array.length_toList, List.length_append, List.length_singleton] at h2
            omega
          | succ n =>
            rw [hkk] at hxk
            simp at hxk
  · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)]
    have he : i - B.size < E.size := by simp at hi2; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [hl]
    refine ⟨[true], ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [(skipBlock_blockMap mask).jump]
      simp [maskKeep]
    · intro k x _ hm
      cases k <;> simp at hm
    · intro k x hx _ u hu
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Array.toList] at hx
        subst hx
        simp [useNums, MInst.operands, MInst.visitOperands] at hu
      | succ k => simp at hx
    · intro k x _ hm
      cases k <;> simp at hm
    · intro _ a ha
      simp at ha

/-- **Spill availability survives the skip of unused instructions** on the prepared code. -/
theorem skipPrepared_spillAvail {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hcls : ClassesOkM vc) (hp : prepare vc = .ok raw) {D : Nat → Nat → Bool}
    (hav : SpillAvail raw D) (hD0 : ∀ v, D 0 v = false) :
    ∃ D', SpillAvail (mapBlocks (skipBlock (stageMask f vc)) raw) D' ∧ ∀ v, D' 0 v = false := by
  rcases stageMask_cases f vc with h | ⟨hl, hchk⟩
  · refine ⟨D, ?_, hD0⟩
    rw [h, mapBlocks_skipBlock_nil]
    exact hav
  · obtain ⟨_, _, _, _, _, _, hS, -⟩ := skipDead_spec hl
    refine ⟨_, skipAvail_of _ (skipBlock_delMap _) raw D hav (fun _ vb hb =>
      (prepSkip_prepare hd hp hS.labels hchk vb
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))).blockOk hcls), ?_⟩
    intro v
    simp [hD0]

/-- **The skip deletes only `skipDel` instructions** of a prepared block, keeping the order. -/
theorem skipPrepared_drop {f : Clif.Function} {vc raw : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok raw) {rb : VBlock} (hrb : rb ∈ raw.blocks.toList) :
    DropSublist skipDel (skipBlock (stageMask f vc) rb).insts.toList rb.insts.toList := by
  rcases stageMask_cases f vc with h | ⟨hl, hchk⟩
  · rw [h, skipBlock_nil]
    exact DropSublist.refl _
  · obtain ⟨_, _, _, _, _, _, hS, -⟩ := skipDead_spec hl
    obtain ⟨m, he, hlen, -, -, hdel, -⟩ := prepSkip_prepare hd hp hS.labels hchk rb hrb
    rw [he]
    exact maskKeep_drop _ _ hlen hdel

end Backend.Proof.Driver
