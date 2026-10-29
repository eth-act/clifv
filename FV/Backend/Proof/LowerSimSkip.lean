import FV.Backend.Proof.VCodeDelete
import FV.Backend.Proof.DriverCheckSound

/-!
# The driver simulation of the VCode without unused statements (`skipDead`)

`skipDead f vc` (`FV/Backend/SkipDead.lean`) deletes from `lowerFunction f`'s VCode `vc` the
segments of `skippable` statements whose results no kept code reads (Cranelift's
`lower_clif_block`, which does not lower such instructions). The argument is at the CLIF level:

* `MatchK s vsK`: the driver relation `Match s vsF` holds of a configuration `vsF` of `vc` that
  corresponds to `vsK` (`CorrC`: same block and world, the kept index of the position, register
  files equal outside the vregs the deleted instructions write);
* a kept statement, a terminator and the entry run only kept instructions (`stmt_run`,
  `term_step_abiP`, `term_step_tryP`, `entry_stepP`), so their runs move to the kept code
  (`starP_deletes`);
* a deleted statement is pure: the CLIF step only binds its results, and the deleted segment's
  run in `vc` (which `Match` asks for) writes only vregs outside the correspondence; the kept code
  takes no step, and the world stays the one of the kept run (`Match` relates the world only
  through `MR slots mem w`, and the memory is unchanged).

No flag reasoning is involved: the deleted compares are never executed in the kept run.
`driver_correct_skip` is `driver_correct` for `skipDead f vc`; `skipDead_spec` provides its
hypotheses from `lowerCheck f vc`.
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

theorem useNums_eq (m : MInst) : useNums m = vuseNums m := rfl
theorem defNums_eq (m : MInst) : defNums m = vdefs m := rfl

/-! ## The deletion check is sound -/

/-- The vregs written by a deleted instruction. -/
def DeadDef (vc : VCode) (mask : Nat → List Bool) (n : Nat) : Prop := n ∈ deadDefs vc mask

theorem mem_zipIdx_of {α : Type} {l : List α} {b : Nat} {x : α} (h : l[b]? = some x) :
    (x, b) ∈ l.zipIdx := by
  rw [List.mem_iff_getElem?]
  exact ⟨b, by simp [List.getElem?_zipIdx, h]⟩

theorem mem_zip_of {α β : Type} {l : List α} {l' : List β} {k : Nat} {x : α} {y : β}
    (h : l[k]? = some x) (h' : l'[k]? = some y) : (x, y) ∈ l.zip l' := by
  rw [List.mem_iff_getElem?]
  exact ⟨k, by simp [List.getElem?_zip_eq_some, h, h']⟩

theorem deadDef_of {vc : VCode} {mask : Nat → List Bool} {b k : Nat} {vb : VBlock} {i : MInst}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hm : (mask b)[k]? = some false)
    {d : Nat} (hd : d ∈ vdefs i) : DeadDef vc mask d := by
  unfold DeadDef deadDefs
  rw [List.mem_flatMap]
  refine ⟨(vb, b), mem_zipIdx_of (by rw [Array.getElem?_toList]; exact hvb), ?_⟩
  rw [List.mem_flatMap]
  exact ⟨(i, false), mem_zip_of (by rw [Array.getElem?_toList]; exact hi) hm, by
    simpa [defNums_eq] using hd⟩

/-- **`deleteCheck` is sound**: the deletion keeps the CFG and no kept code reads a vreg that a
deleted instruction writes. -/
theorem deletes_of_check {vc : VCode} {mask : Nat → List Bool} (h : deleteCheck vc mask = true) :
    Deletes vc (deleteWith vc mask) mask (DeadDef vc mask) := by
  unfold deleteCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hcfg⟩ := h
  have hb := fun b vb (hvb : vc.blocks[b]? = some vb) =>
    hall (vb, b) (mem_zipIdx_of (by rw [Array.getElem?_toList]; exact hvb))
  refine ⟨fun b vb hvb => ⟨{ vb with insts := (maskKeep (mask b) vb.insts.toList).toArray },
      by simp [deleteWith, Array.getElem?_mapIdx, hvb], by simp, rfl, rfl⟩,
    fun b vb hvb => ?_, fun b vb hvb => ?_, ?_, fun b vb k i hvb hi hm u hu => ?_,
    fun b vb r n hvb hr hrn => ?_⟩
  · exact beq_iff_eq.mp (hb b vb hvb).1.1.1
  · have := (hb b vb hvb).1.1.2
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · unfold cfgSame at hcfg
    split at hcfg
    · rename_i x y hx hy
      rw [hx, hy, beq_iff_eq.mp hcfg]
    · cases hcfg
  · have h3 := (hb b vb hvb).1.2 (i, true)
      (mem_zip_of (by rw [Array.getElem?_toList]; exact hi) hm)
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true, Bool.not_eq_true'] at h3
    intro hd
    have h5 : (deadDefs vc mask).contains u = true := List.contains_iff_mem.mpr hd
    rw [h3 u (by rw [useNums_eq]; exact hu)] at h5
    cases h5
  · have h4 := (hb b vb hvb).2 r hr
    rw [hrn] at h4
    simp only [Bool.not_eq_true'] at h4
    intro hd
    have : (deadDefs vc mask).contains n = true := List.contains_iff_mem.mpr hd
    rw [this] at h4; cases h4

/-! ## The mask of the skipped statements -/

section
variable {f : Clif.Function} {vc : VCode} {R : Reg → Reg} {bl : List BLow}

theorem sum_range_le (g : Nat → Nat) : ∀ {j n : Nat}, j ≤ n →
    ((List.range j).map g).sum ≤ ((List.range n).map g).sum
  | _, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | j, n + 1, h => by
    rcases Nat.lt_or_ge j (n + 1) with hj | hj
    · have := sum_range_le g (j := j) (n := n) (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]
      omega
    · rw [show j = n + 1 by omega]; exact Nat.le_refl _

theorem flattenRep_length {α : Type} (len : Nat → Nat) (x : Nat → α) (n : Nat) :
    (((List.range n).map fun j => List.replicate (len j) (x j)).flatten).length =
      ((List.range n).map len).sum := by
  rw [List.length_flatten, List.map_map]; simp [Function.comp_def]

theorem flattenRep_getElem? {α : Type} (len : Nat → Nat) (x : Nat → α) :
    ∀ {n j t : Nat}, j < n → t < len j →
      (((List.range n).map fun j => List.replicate (len j) (x j)).flatten)[
        ((List.range j).map len).sum + t]? = some (x j)
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, t, hj, ht => by
    rw [List.range_succ, List.map_append, List.flatten_append]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · have hlt : ((List.range j).map len).sum + t <
          (((List.range n).map fun j => List.replicate (len j) (x j)).flatten).length := by
        rw [flattenRep_length]
        have h1 := sum_range_le len (show j + 1 ≤ n by omega)
        rw [List.range_succ, List.map_append, List.sum_append] at h1
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
        omega
      rw [List.getElem?_append_left hlt]
      exact flattenRep_getElem? len x hjn ht
    · have hjn' : j = n := by omega
      subst hjn'
      rw [List.getElem?_append_right (by rw [flattenRep_length]; omega), flattenRep_length,
        Nat.add_sub_cancel_left]
      simp [ht]

/-- The mask of an original block at a statement's segment: `!drop b j`. -/
theorem skipMask_seg {drop : Nat → Nat → Bool} {b j t : Nat} {B : Clif.Block}
    (hB : f.blocks[b]? = some B) (hj : j < B.body.length) (ht : t < (seg f R bl b j).length) :
    (skipMask f R bl vc drop b)[pos f R bl b j + t]? = some (!drop b j) := by
  unfold skipMask pos
  rw [hB]
  simp only
  have hF := flattenRep_length (fun j => (seg f R bl b j).length) (fun j => !drop b j)
    B.body.length
  have hle := sum_range_le (fun j => (seg f R bl b j).length) (show j + 1 ≤ B.body.length by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at hle
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hle
  rw [List.append_assoc, List.getElem?_append_right (by simp only [List.length_replicate]; omega),
    List.length_replicate,
    show (pre f R b).length + ((List.range j).map fun j' => (seg f R bl b j').length).sum + t -
      (pre f R b).length = ((List.range j).map fun j' => (seg f R bl b j').length).sum + t by omega,
    List.getElem?_append_left (by rw [hF]; omega)]
  exact flattenRep_getElem? (fun j => (seg f R bl b j).length) (fun j => !drop b j) hj ht

/-- The mask of an original block at its terminator's code: kept. -/
theorem skipMask_tseg {drop : Nat → Nat → Bool} {b t : Nat} {B : Clif.Block}
    (hB : f.blocks[b]? = some B) (ht : t < (tseg R bl b).length) :
    (skipMask f R bl vc drop b)[pos f R bl b B.body.length + t]? = some true := by
  unfold skipMask pos
  rw [hB]
  simp only
  have hF := flattenRep_length (fun j => (seg f R bl b j).length) (fun j => !drop b j)
    B.body.length
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_replicate]; omega),
    List.length_append, List.length_replicate, hF]
  simp [ht]

/-- The mask of an original block at its entry code: kept. -/
theorem skipMask_pre {drop : Nat → Nat → Bool} {b t : Nat} {B : Clif.Block}
    (hB : f.blocks[b]? = some B) (ht : t < (pre f R b).length) :
    (skipMask f R bl vc drop b)[t]? = some true := by
  unfold skipMask
  rw [hB]
  simp only
  rw [List.append_assoc, List.getElem?_append_left (by simpa using ht)]
  simp [ht]

end

/-! ## The simulation -/

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)} {drop : Nat → Nat → Bool}

/-- The statement `j` of block `b` exists and is `skippable` when `drop b j`. -/
def SkipOk (f : Clif.Function) (drop : Nat → Nat → Bool) : Prop :=
  ∀ b j B stm, drop b j = true → f.blocks[b]? = some B → B.body[j]? = some stm →
    skippable stm.inst = true

/-- **The hypotheses of the skipped-statement simulation**: `vcK` is `vc` with the segments of
`drop` deleted (`skipMask`), the deletion check passes, and the deleted statements are
`skippable`. -/
structure SkipHyp (f : Clif.Function) (vc : VCode) (R : Reg → Reg) (bl : List BLow)
    (drop : Nat → Nat → Bool) (vcK : VCode) : Prop where
  eq : vcK = deleteWith vc (skipMask f R bl vc drop)
  check : deleteCheck vc (skipMask f R bl vc drop) = true
  skip : SkipOk f drop

/-- **The relation of the kept code**: `Match` of a corresponding configuration of `vc`. -/
def MatchK (f : Clif.Function) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
    (A : Nat → Nat → List Clif.ValueId) (MR : MemRelTW W) (slots : List (Clif.SlotId × Nat))
    (mask : Nat → List Bool) (G : Nat → Prop) (s : Clif.State) (vsK : VState CV W) : Prop :=
  ∃ vsF : VState CV W, CorrC mask G (.run vsF) (.run vsK) ∧ Match f ctx R gn bl A MR slots s vsF

theorem match_world {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w w' : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hmr : MR slots s.mem w') :
    Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w'⟩ := by
  obtain ⟨h1, h2, h3, -, h5⟩ := hm
  exact ⟨h1, h2, h3, hmr, h5⟩

theorem pureInst_of_skippable {i : Clif.Inst} (h : skippable i = true) : pureInst i = true := by
  cases i <;> simp_all [skippable, pureInst]

theorem explicitTrapInst_of_skippable {i : Clif.Inst} (h : skippable i = true) :
    explicitTrapInst i = false := by
  cases i <;> simp_all [skippable, explicitTrapInst]

/-- A `skippable` statement's step keeps the memory. -/
theorem skip_step_mem {s s' : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (hbody : s.frame.body = stm :: rest) (hsk : skippable stm.inst = true)
    (hs : Clif.step env p s = .next s') : s'.mem = s.mem := by
  have hp := pureInst_of_skippable hsk
  rw [step_stmt env p s stm rest hbody
    (fun fn args hi => by rw [hi] at hsk; simp [skippable] at hsk)
    (fun sig callee args hi => by rw [hi] at hsk; simp [skippable] at hsk),
    instOutcome_of_pure hp] at hs
  cases hO : Clif.evalInst s.frame s.mem stm.inst with
  | ok r =>
    obtain ⟨vals, cm'⟩ := r
    rw [hO] at hs
    simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs
    split at hs
    · cases hs
      exact (evalInst_pure hp hO).1
    · cases hs
  | trap c => rw [hO] at hs; cases hs
  | stuck m => rw [hO] at hs; cases hs

variable (hK : SkipHyp f vc R bl drop vcK)
include hK

theorem SkipHyp.deletes :
    Deletes vc vcK (skipMask f R bl vc drop) (DeadDef vc (skipMask f R bl vc drop)) :=
  hK.eq ▸ deletes_of_check hK.check

/-- A position in a TermZone of an original block's terminator code is kept. -/
theorem termZone_kept (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {b : Nat}
    {B : Clif.Block} (hB : f.blocks[b]? = some B) :
    ∀ b' k ρ w, TermZone (W := W) vc b (pos f R bl b B.body.length) (.run ⟨b', k, ρ, w⟩) →
      ∀ vb i, vc.blocks[b']? = some vb → vb.insts[k]? = some i →
        (skipMask f R bl vc drop b')[k]? = some true := by
  intro b' k ρ w hz vb i hvb hi
  rcases hz with ⟨k', ρ', w', he, hle⟩ | ⟨e, ρ', w', vb', l, he, hvb', hins⟩
  · simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    obtain ⟨L, hL⟩ := H.blow hB
    obtain ⟨vb0, hvb0, -, -, -, -, -, -, hcode, -, -⟩ := H.shape.blk b' B L hB hL
    rw [hvb] at hvb0; cases hvb0
    have hlt : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hsz : vb.insts.size = pos f R bl b' B.body.length + (tseg R bl b').length :=
      (tseg_at hcode).2
    have := skipMask_tseg (vc := vc) (R := R) (bl := bl) (drop := drop)
      (t := k - pos f R bl b' B.body.length) hB
      (by omega)
    rwa [Nat.add_sub_cancel' hle] at this
  · simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    rw [hvb] at hvb'; cases hvb'
    have hD := hK.deletes
    have hlen := hD.len b' vb hvb
    rcases hD.last b' vb hvb with h0 | hl
    · rw [hins] at h0; cases h0
    · rw [hins] at hlen
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hlen
      rw [List.getLast?_eq_getElem?, hlen] at hl
      exact hl

/-- **Statement step of the kept code.** -/
theorem stmt_stepK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vsK', Star (VStep vcK sem) (.run vsK) (.run vsK') ∧
        MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' vsK') ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vcK sem vsK c) := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, -, hjlt, hstm, rfl, hnext, htrap⟩ := stmt_run H hM hbody hind
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨hsegat, hlt⟩ := seg_at hcode htne hjlt
  have hP : ∀ b' k' ρ' w', AtSeg (V := CV) (W := W) b (pos f R bl b j) (seg f R bl b j).length
      (.run ⟨b', k', ρ', w'⟩) → drop b j = false → ∀ vb' i, vc.blocks[b']? = some vb' →
        vb'.insts[k']? = some i → (skipMask f R bl vc drop b')[k']? = some true := by
    rintro b' k' ρ' w' ⟨t, ht, ρ'', w'', he⟩ hdrop vb' i - -
    simp only [VConf.run.injEq, VState.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    rw [skipMask_seg hB hjlt ht, hdrop]; rfl
  cases hdrop : drop b j with
  | false =>
    refine ⟨fun s' hs => ?_, fun c hs hexp => ?_⟩
    · obtain ⟨ρ', w', hsr, hM'⟩ := hnext s' hs
      rw [pos_succ] at hlt hM'
      have hstar := seqRun_fall_starP (vc := vc) (sem := sem) hvb hsegat hlt hsr
      obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD (fun b' k' ρ' w' h => hP b' k' ρ' w' h hdrop)
        hstar _ hC
      cases cK with
      | run vsK' => exact ⟨vsK', hsK, _, hCK, hM'⟩
      | ret _ _ => exact absurd hCK id
      | halt _ => exact absurd hCK id
    · obtain ⟨k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := htrap c hs hexp
      obtain ⟨hstar, hk', hi, hops, hsem, -, -⟩ := seqRun_stop_starP (vc := vc) hvb hsegat hsr
      exact VTrapFromP.deletes hD (fun b' k' ρ' w' h => hP b' k' ρ' w' h hdrop)
        ⟨b, _, ρ₁, w₁, vb, i, ops, outs, w₂, hstar, ⟨k', hk', ρ₁, w₁, rfl⟩, hvb, hi, hops, hsem,
          htc⟩ hC
  | true =>
    have hsk := hK.skip b j B stm hdrop hB hstm
    refine ⟨fun s' hs => ?_, fun c _ hexp => ?_⟩
    · obtain ⟨ρ', w', hsr, hM'⟩ := hnext s' hs
      have hmem := skip_step_mem hbody hsk hs
      obtain ⟨hb, hk, hw, hρ⟩ := hC
      simp only at hb hk hw hρ
      refine ⟨vsK, .refl _, ⟨b, pos f R bl b (j + 1), ρ', w⟩, ⟨hb, ?_, hw, ?_⟩,
        match_world hM' (by rw [hmem]; exact hM.2.2.2.1)⟩
      · rw [hk, pos_succ]
        exact (kidx_false_range (fun t ht => by
          have := skipMask_seg (vc := vc) (drop := drop) hB hjlt ht
          rw [hdrop] at this; exact this)).symm
      · intro n hn
        rw [← hρ n hn]
        refine seqRun_fall_frame (fun m hm hnm => hn ?_) hsr
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hm
        refine deadDef_of hvb (hsegat t ht) ?_ hnm
        have := skipMask_seg (vc := vc) (drop := drop) hB hjlt ht
        rw [hdrop] at this; exact this
    · rw [explicitTrapInst_of_skippable hsk] at hexp; cases hexp

/-- **Terminator step of the kept code** (with the ABI return values). -/
theorem term_step_abiK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vsK', Star (VStep vcK sem) (.run vsK) (.run vsK') ∧
        MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
          (DeadDef vc (skipMask f R bl vc drop)) s' vsK') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vcK sem vsK us outs w' ∧
        RetPins vals us ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vcK sem vsK c) := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hj, hbd, hk⟩ : ∃ B j, f.blocks[b]? = some B ∧ j ≤ B.body.length ∧
      s.frame.body = B.body.drop j ∧ k = pos f R bl b j :=
    let ⟨_, _, _, _, B, j, hB, _, hj, hbd, hk, _⟩ := hM; ⟨B, j, hB, hj, hbd, hk⟩
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  subst hk
  have hP := termZone_kept hK H (W := W) hB
  obtain ⟨T1, T2, T3⟩ := term_step_abiP H hM hbody hnt
  refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c hs => VTrapFromP.deletes hD hP (T3 c hs) hC⟩
  · obtain ⟨vs', hstar, hM'⟩ := T1 s' hs
    obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hstar _ hC
    cases cK with
    | run vsK' => exact ⟨vsK', hsK, _, hCK, hM'⟩
    | ret _ _ => exact absurd hCK id
    | halt _ => exact absurd hCK id
  · obtain ⟨us, outs, w', sv, hr, h1⟩ := T2 vals cm hs
    exact ⟨us, outs, w', sv, VRetFromP.deletes hD hP hr hC, h1⟩

/-- **`try_call` step of the kept code.** -/
theorem term_step_tryK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {vsK : VState CV W}
    (hm : MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
      (DeadDef vc (skipMask f R bl vc drop)) s vsK) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ vsK', Star (VStep vcK sem) (.run vsK) (.run vsK') ∧
          MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
            (DeadDef vc (skipMask f R bl vc drop)) s'' vsK' := by
  have hD := hK.deletes
  obtain ⟨⟨b, k, ρ, w⟩, hC, hM⟩ := hm
  obtain ⟨B, j, hB, hj, hbd, hk⟩ : ∃ B j, f.blocks[b]? = some B ∧ j ≤ B.body.length ∧
      s.frame.body = B.body.drop j ∧ k = pos f R bl b j :=
    let ⟨_, _, _, _, B, j, hB, _, hj, hbd, hk, _⟩ := hM; ⟨B, j, hB, hj, hbd, hk⟩
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  subst hk
  have hP := termZone_kept hK H (W := W) hB
  obtain ⟨T1, T2⟩ := term_step_tryP H hM hbody hT hind
  refine ⟨T1, fun s' hs => ?_⟩
  obtain ⟨N1, N2, N3⟩ := T2 s' hs
  refine ⟨N1, N2, fun s'' hs' => ?_⟩
  obtain ⟨vs', hstar, hM'⟩ := N3 s'' hs'
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hstar _ hC
  cases cK with
  | run vsK' => exact ⟨vsK', hsK, _, hCK, hM'⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

/-- **Whole runs of the kept code**, with the ABI return values (`sim_run_abi`). -/
theorem sim_run_abiK (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (hP : RunPrem env p f cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → Q sv) :
    ∀ fuel s (vs : VState CV W), Reach env p cs s →
      MatchK f ctx R gn bl A MR slots (skipMask f R bl vc drop)
        (DeadDef vc (skipMask f R bl vc drop)) s vs →
        RunOkAbi vcK sem MR slots Q vs (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s vs hr hm
  cases fuel with
  | zero => trivial
  | succ n =>
    rw [Clif.runLoop_succ]
    obtain ⟨vsF, -, hMF⟩ := id hm
    have hfunc : s.frame.func = f := hMF.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_step_abiK hK H hm hbody hty
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨vs', hstar, hm'⟩ := T1 s' hs
          exact RunOkAbi.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, w', s.mem, sv, hret, h1, h2, hQ s sv hr hsv, h3, h4, h5⟩
        | trapped c => exact T3 c hs
        | stuck => trivial
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hMF.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
          cases ht : s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => hP.tryIndirect s callee args et hr hbody ht ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryK hK H hm hbody hT hind
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨N1, N2, N3⟩ := Tnx s' hs
          cases n with
          | zero => trivial
          | succ m =>
            show RunOkAbi vcK sem MR slots Q _ (Clif.runLoop env p (m + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs'
              exact RunOkAbi.prefix hstar (ih m (by omega) s'' vs' ((hr.snoc hs).snoc hs') hm')
            | done vals cm => exact absurd hs' (N2 vals cm)
            | trapped c => exact absurd hs' (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd hs (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT) (hP.tryCall s c fn args et hr hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr hs hbody hT B hBmem)
        | stuck => trivial
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hMF
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact H.ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      obtain ⟨S1, S2⟩ := stmt_stepK hK H hm hbody hind
      cases hs : Clif.step env p s with
      | next s' =>
        obtain ⟨vs', hstar, hm'⟩ := S1 s' hs
        exact RunOkAbi.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
      | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
      | trapped c => exact S2 c hs (hP.stmt s c st rest hr hs hbody)
      | stuck => trivial

end

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool}

/-- The position after the entry code is the entry code's length. -/
theorem pos_of_drop_eq {b j : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (h : B.body.drop j = B.body) : pos f R bl b j = (pre f R b).length := by
  unfold pos
  have hz : ∀ j' < j, (seg f R bl b j').length = 0 := by
    intro j' hj'
    have hlen := congrArg List.length h
    rw [List.length_drop] at hlen
    have : B.body[j']? = none := by
      rw [List.getElem?_eq_none_iff]; omega
    unfold seg
    rw [hB]
    cases bl[b]? <;> simp [this]
  have hsum : ∀ m ≤ j, ((List.range m).map fun j' => (seg f R bl b j').length).sum = 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [hz m (by omega)]
  rw [hsum j (Nat.le_refl _), Nat.add_zero]

/-- **The driver lemma for the kept code, with the ABI return values** (`driver_correct_abi` for
`vcK`, the VCode without the unused statements). -/
theorem driver_correct_abi_skip (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → Q sv) (fuel : Nat) :
    RunOkAbi vcK sem MR slots Q ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  have hD := hK.deletes
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_stepP H hds hMem hMR hB0 hcall hfunc hslots hbody hterm
    hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  have hk : k = (pre f R 0).length := by
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, hk', -⟩ := hm
    rw [hB0] at hB; cases hB
    simp only at hk'
    rw [hk', pos_of_drop_eq hB0 (by rw [← hbd, hbody])]
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD (fun b k' ρ w hz vb i _ _ => by
      obtain ⟨t, ht, ρ', w', he⟩ := hz
      simp only [VConf.run.injEq, VState.mk.injEq] at he
      obtain ⟨rfl, rfl, -, -⟩ := he
      exact skipMask_pre hB0 (by rw [← hk]; simpa using ht))
    hstar (.run ⟨0, 0, ρ₀, w₀⟩) ⟨rfl, by simp, rfl, fun _ _ => rfl⟩
  cases cK with
  | run vsK => exact RunOkAbi.prefix hsK (sim_run_abiK hK H hP hQ fuel cs vsK (.refl _) ⟨_, hCK, hm⟩)
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

/-- **The driver lemma for the kept code** (`driver_correct` for `vcK`). -/
theorem driver_correct_skip (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hK : SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) (fuel : Nat) :
    RunOk vcK sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) :=
  (driver_correct_abi_skip H hK hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
    hargs hP (Q := fun _ => True) (fun _ _ _ _ => trivial) fuel).runOk

end

/-! ## `skipDead` provides the hypotheses -/


theorem skipOk_skipAt (f : Clif.Function) (drop : Nat → Nat → Bool) : SkipOk f (skipAt f drop) := by
  intro b j B stm h hB hstm
  simp only [skipAt, hB, hstm, Bool.and_eq_true] at h
  exact h.2

/-- **`skipDead` provides the hypotheses**: if the lowering validator accepts `vc`, the lowering
obligations hold for `vc`, and `skipDead f vc` is `vc` or the deletion `SkipHyp` describes it,
for the same renaming and lowering record. -/
theorem skipDead_spec {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧
      (skipDead f vc = vc ∨
        SkipHyp f vc R bl (skipAt f (skipDrops f R bl vc)) (skipDead f vc)) := by
  unfold lowerCheck at h
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    split at h
    · cases h
    · rename_i bl hl
      simp only [Bool.and_eq_true] at h
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      refine ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2, ?_⟩
      unfold skipDead
      rw [hb]
      simp only
      rw [hl]
      simp only
      split
      · rename_i hc
        exact .inr ⟨rfl, hc, skipOk_skipAt f _⟩
      · exact .inl rfl

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The driver lemma for `skipDead f vc`** (`driver_correct` or `driver_correct_skip`, as
`skipDead_spec` says). -/
theorem driver_correct_skipDead (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hsk : skipDead f vc = vc ∨
      SkipHyp f vc R bl (skipAt f (skipDrops f R bl vc)) (skipDead f vc)) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) (fuel : Nat) :
    RunOk (skipDead f vc) sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  rcases hsk with he | hK
  · rw [he]
    exact driver_correct H hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs
      hP fuel
  · exact driver_correct_skip H hK hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig
      hmr hargs hP fuel

end

/-! ## Non-vacuity -/

/-- The witness's source: the `icmp` is only read by the `brif`, whose rule compares again
(`lower_branch (brif (maybe_uextend (icmp ...)))`), so its `cmp; cset` is unused. -/
def skipWitnessSrc : String := "function %w(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = icmp eq v0, v1
    brif v2, block1, block2
block1:
    return v0
block2:
    return v1
}"

/-- The witness function. -/
def skipWitness : Clif.Function :=
  match (Clif.parseFile skipWitnessSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

/-- The witness lowers, the validator accepts it, and `skipDead` deletes instructions. -/
theorem skipWitness_checks :
    (match lowerFunction skipWitness with
      | .ok vc => lowerCheck skipWitness vc &&
          ((skipDead skipWitness vc).blocks.toList.map (·.insts.size) !=
            vc.blocks.toList.map (·.insts.size))
      | .error _ => false) = true := by
  native_decide

/-- **Non-vacuity of `driver_correct_skip`**: on `skipWitness`, the validator accepts the lowering
and `skipDead` deletes instructions, so `SkipHyp` holds with a VCode different from the lowering. -/
theorem skipHyp_witness : ∃ vc R bl drop vcK, lowerFunction skipWitness = .ok vc ∧
    lowerCheck skipWitness vc = true ∧ SkipHyp skipWitness vc R bl drop vcK ∧ vcK ≠ vc := by
  have h := skipWitness_checks
  cases hl : lowerFunction skipWitness with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hc, hne⟩ := h
    obtain ⟨-, -, R, -, bl, -, -, -, -, hsk⟩ := skipDead_spec hc
    rcases hsk with he | hK
    · rw [he] at hne; exact absurd rfl hne
    · exact ⟨vc, R, bl, _, _, rfl, hc, hK, fun he => hne (by rw [he])⟩

end Backend.Proof.Driver
