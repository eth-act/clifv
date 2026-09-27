import FV.Backend.Proof.LowerLemmas

/-!
# The driver simulation: CLIF steps ↦ VCode steps (M7)

`Match s vs`: the CLIF state `s` (one activation of `f`, no callers) is at statement `j` of
block `bi`, the VCode state `vs` at the start of that statement's segment; every tracked value
(`A bi j`) is held (low bits) by its resolved vreg `gn x`; the restriction of the frame to the
tracked values is DFG-consistent; memory and world are related by `MR`.

* `stmt_step`: a CLIF statement step is matched by the straight-line run of its segment (or,
  for an explicit trap, reaches the halting instruction);
* `term_step`: returns, traps, and branches (jump arguments as the VCode parallel copy, edge
  blocks for `brif`/`br_table` arguments);
* `entry_step`: the entry `Args`;
* `sim_run`: whole runs (`Clif.runLoop`).
-/

namespace Backend.Proof.Driver

open Backend

/-- Every tracked value is held by its resolved vreg. -/
def Held (gn : Nat → Nat) (A : List Clif.ValueId) (ρ : Nat → CV) (fr : Clif.Frame) : Prop :=
  ∀ x ∈ A, ∃ v, fr.regs x = some v ∧ VHolds v (ρ (gn x))

/-- The simulation relation. -/
def Match (f : Clif.Function) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
    (A : Nat → Nat → List Clif.ValueId) (MR : MemRelT) (slots : List (Clif.SlotId × Nat))
    (s : Clif.State) (vs : VState CV Arm.ArmState) : Prop :=
  s.callers = [] ∧ s.frame.func = f ∧ s.frame.slots = slots ∧ MR slots s.mem vs.w ∧
  ∃ B j, f.blocks[vs.b]? = some B ∧ s.frame.term = B.term ∧ j ≤ B.body.length ∧
    s.frame.body = B.body.drop j ∧ vs.k = pos f R bl vs.b j ∧
    Held gn (A vs.b j) vs.ρ s.frame ∧ DFGCons ctx (restrict s.frame (A vs.b j))

/-- From `vs`, the VCode run reaches an instruction that halts with trap code `c`. -/
def VTrapFrom (vc : VCode) (sem : Sem) (vs : VState CV Arm.ArmState) (c : Clif.TrapCode) : Prop :=
  ∃ b k ρ w vb i ops outs w', Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    sem i (vuses ops ρ) w = some (outs, w', .halt) ∧ trapCode? i = some c

/-- From `vs`, the VCode run executes `rets us` with use values `vals`, final world `w`. -/
def VRetFrom (vc : VCode) (sem : Sem) (vs : VState CV Arm.ArmState) (us : List (Reg × Reg))
    (vals : List CV) (w : Arm.ArmState) : Prop :=
  ∃ b k ρ w₁ vb ops outs, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w₁⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) ∧
    (MInst.rets us).operands = .ok ops ∧ vals = vuses ops ρ ∧
    sem (.rets us) vals w₁ = some (outs, w, .ret)

theorem VTrapFrom.prefix {vc : VCode} {sem : Sem} {vs vs' : VState CV Arm.ArmState}
    {c : Clif.TrapCode} (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VTrapFrom vc sem vs' c) :
    VTrapFrom vc sem vs c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', h.trans hs, h1⟩

theorem VRetFrom.prefix {vc : VCode} {sem : Sem} {vs vs' : VState CV Arm.ArmState}
    {us : List (Reg × Reg)} {vals : List CV} {w : Arm.ArmState}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VRetFrom vc sem vs' us vals w) :
    VRetFrom vc sem vs us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w₁, vb, ops, outs, h.trans hs, h1⟩

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow}

/-! ## Segments -/

theorem seg_eq {bi j : Nat} {B : Clif.Block} {L : BLow} {stm : Clif.Stmt} {sl : SLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (hs : B.body[j]? = some stm)
    (hsl : L.sl[j]? = some sl) :
    seg f R bl bi j = (sl.st'.emitted.toList ++ extraOf stm.results sl.rss).map (·.mapRegs R) := by
  simp [seg, hB, hL, hs, hsl]

theorem tseg_eq {bi : Nat} {L : BLow} (hL : bl[bi]? = some L) :
    tseg R bl bi = L.tst'.emitted.toList.map (·.mapRegs R) := by
  simp [tseg, hL]

theorem pos_succ (bi j : Nat) : pos f R bl bi (j + 1) = pos f R bl bi j + (seg f R bl bi j).length := by
  simp [pos, List.range_succ, Nat.add_assoc]

theorem seg_at {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi) (htne : tseg R bl bi ≠ []) {j : Nat} (hj : j < B.body.length) :
    SegAt vb (pos f R bl bi j) (seg f R bl bi j) ∧ pos f R bl bi (j + 1) < vb.insts.size := by
  have hsplit := flatten_range_split (seg f R bl bi) hj
  rw [hsplit] at hcode
  have hlen : (pre f R bi ++ ((List.range j).map (seg f R bl bi)).flatten).length = pos f R bl bi j := by
    simp [pos, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have : vb.insts.toList = (pre f R bi ++ ((List.range j).map (seg f R bl bi)).flatten) ++
        seg f R bl bi j ++ ((((List.range (B.body.length - (j + 1))).map
          fun i => seg f R bl bi (j + 1 + i))).flatten ++ tseg R bl bi) := by
      rw [hcode]; simp [List.append_assoc]
    have h := segAt_of_toList this
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, pos_succ, ← hlen]
    have : 0 < (tseg R bl bi).length := List.length_pos_iff.mpr htne
    simp only [List.length_append]
    omega

theorem tseg_at {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi) :
    SegAt vb (pos f R bl bi B.body.length) (tseg R bl bi) ∧
      vb.insts.size = pos f R bl bi B.body.length + (tseg R bl bi).length := by
  have hlen : (pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten).length =
      pos f R bl bi B.body.length := by
    simp [pos, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have h := segAt_of_toList (L₂ := []) (by rw [hcode, List.append_nil])
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, List.length_append, hlen]

theorem extraOf_nil {results : List Nat} {rss : List (List Reg)}
    (h : ∀ (k : Nat) rs, rss[k]? = some rs → ∃ out cls, rs = [.vreg out cls]) :
    extraOf results rss = [] := by
  unfold extraOf
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  obtain ⟨k, hk⟩ := List.getElem_of_mem hp
  obtain ⟨hk1, hk2⟩ := hk
  have := List.getElem?_eq_getElem (l := results.zip rss) hk1
  rw [hk2] at this
  have hr : rss[k]? = some p.2 := by
    rw [List.getElem?_zip_eq_some] at this
    exact this.2
  obtain ⟨out, cls, he⟩ := h k p.2 hr
  obtain ⟨r, rs⟩ := p
  simp only at he
  subst he
  rfl

end

end Backend.Proof.Driver
