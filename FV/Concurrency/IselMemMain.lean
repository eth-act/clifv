import FV.Concurrency.CEvsInv
import FV.Concurrency.IselMemLower

/-!
# The segment of a memory statement (T2h, #311, layer 2e)

**`mem_seg`**: from a match at a memory statement (`load`, `store`, `atomic_*`, `fence`), a
VCode thread run is realized (`IselThread.SegRes`):

* if the CLIF statement steps on no bytes, the CLIF thread has no step (`Done`); an
  `atomic_cas` on read-only data is outside the scope (`CasRO`);
* else the thread walks to the statement's one memory instruction without events
  (`IselSeg.vtrun_walk`); with the CLIF access holding the world's own bytes (`IselSeg.mr_own`),
  the run of the code reaches the instruction where its footprint is the CLIF access
  (`IselMemLower.mem_vreg`); the thread is there (determinism), so the thread step's events are at
  the access (`CEvsInv.cEvs_setMem_atA`);
* both memories patched with the bytes the thread read keep the match (`MemRelOk.store`), the
  CLIF statement steps there (`IselMemLower.step_next_of`) and the driver's step from the
  patched pair (`IselStep.stmt_matchN`) is the thread's segment (`IselMemSeg.mem_complete`);
* the CLIF step reading those bytes (`ClifCStep`) has the thread's events: reads hold the patched
  bytes (`IFoot`'s agreement), writes the bytes the memory relation pins after the segment
  (`IselMemHelp.bytes_of_mr`); an `atomic_cas` writes exactly when its loop does
  (`IselMemLower.cas_cmp`, the loop comparing with the expected value's vreg, `casOkB`).
-/

namespace Concurrency.IselMemMain

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm IselThread IselMem Code
  IselMemSeg IselMemHelp IselMemLower VCodeAddr ClifCStep ArmInstFoot IselClif

theorem isRetsB_mapRegs (R : Reg → Reg) (i : MInst) : isRetsB (i.mapRegs R) = isRetsB i := by
  cases i <;> rfl

theorem notRets_of_instOkB {i : MInst} (h : instOkB i = true) : isRetsB i = false := by
  simp only [instOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem covered_of_instOkB {fc : FnCtx} {i : MInst} (h : instOkB i = true) : SegFoot.Covered fc i := by
  simp only [instOkB, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨hc, hcall⟩, -⟩ := h
  refine ⟨fun info e => ?_, fun info ti e => ?_, ?_⟩
  · subst e; simp [isCallB] at hcall
  · subst e; simp [isCallB] at hcall
  · rcases hc with h | h
    · exact .inl h
    · exact .inr (by simpa [FormOk] using h)

/-- The result copies of a statement's code have no memory kind and are not `rets`. -/
theorem extra_facts {results : List Nat} {rss : List (List Reg)} {i : MInst}
    (h : i ∈ extraOf results rss) : akinds i = [] ∧ isRetsB i = false := by
  unfold extraOf at h
  obtain ⟨⟨r, rs⟩, -, hh⟩ := List.mem_filterMap.mp h
  simp only at hh
  split at hh
  · cases hh
  · cases hh; exact ⟨by simp [akinds], rfl⟩
  · cases hh

/-- A VCode thread step: its events are the footprint on the patched world. -/
theorem vtstep_evs {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {b k : Nat} {ρ : Nat → CV} {w : ArmState} {evs : List Ev} {c' : VConf CV ArmState}
    (h : VTStep vc sem ev (.run ⟨b, k, ρ, w⟩) evs c') :
    ∃ vb i ops, vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      evs = ev i (vuses ops ρ) (patch evs w) ∧ IFoot sem i (vuses ops ρ) (patch evs w) evs ∧
      VStep vc sem (.run ⟨b, k, ρ, patch evs w⟩) c' := by
  cases h with
  | mk hb hi hops he hf hst => exact ⟨_, _, _, hb, hi, hops, he, hf, hst⟩

theorem single_of_sublist {E : List Ev} {x : AKind} (h : List.Sublist (E.map (·.k)) [x])
    (hne : E ≠ []) :
    ∃ e, E = [e] ∧ e.k = x := by
  rcases E with _ | ⟨e, _ | ⟨e', t⟩⟩
  · exact absurd rfl hne
  · exact ⟨e, rfl, by simpa using h⟩
  · have := h.length_le; simp at this

/-- A read event at the access, as a program event. -/
theorem conv_at {e : Ev} {M : Memory} (h : readM e.n e.addr M = e.val) {a n : Nat}
    (hA : e.addr = BitVec.ofNat 64 a) (hn : e.n = n) (ha : a < 2 ^ 64) :
    (ProgE2E.convEv e).loc = a ∧ (ProgE2E.convEv e).n = n ∧
      (ProgE2E.convEv e).val = ProgE2E.bytesOf n (readM n (BitVec.ofNat 64 a) M) := by
  obtain ⟨k, addr, n', val⟩ := e
  simp only at hA hn h
  subst hA hn h
  simp [ProgE2E.convEv, Nat.mod_eq_of_lt ha]

theorem loc_at {e : Ev} {a : Nat} (hA : e.addr = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    (ProgE2E.convEv e).loc = a := by
  simp [ProgE2E.convEv, hA, Nat.mod_eq_of_lt ha]

theorem getB_valB_some {B : Bytes} {a n w : Nat} {big : Bool} {v : BitVec w}
    (h : getB B a n = valB big n v) : ∀ k < n, (B (a + k)).isSome := by
  intro k hk
  have e := congrArg (·[k]?) h
  simp only [getB, valB, List.getElem?_map, List.getElem?_range hk, Option.map_some] at e
  injection e with e
  rw [e]; rfl

theorem writeBits_isSome (m : Clif.Mem) {w : Nat} (big : Bool) (a n : Nat) (v : BitVec w) :
    ∀ j < n, ((m.writeBits big a n v).bytes (a + j)).isSome := by
  intro j hj
  simp only [Clif.Mem.writeBits]
  rw [if_pos (show a ≤ a + j ∧ a + j < a + n by omega)]
  rfl

theorem valid_of_allocs {c c' : Clif.Mem} (h : c'.allocs = c.allocs) {a n : Nat}
    (hv : c.valid a n = true) : c'.valid a n = true := by
  simp only [Clif.Mem.valid] at hv ⊢
  rw [h]; exact hv

theorem expect_dmb {inst : Clif.Inst} {ks : List AKind} {nE : Nat}
    (he : SegShape.expect inst = some (ks, nE)) (hk : ks = [.dmb]) : inst = .fence := by
  subst hk
  cases inst <;> simp [SegShape.expect] at he ⊢

theorem pw_one {x : Prog.Ev SKind BVal} {y : Prog.Ev AKind BVal} (h : EvRel Maps x y) :
    PW (EvRel Maps) [x] [y] :=
  ⟨rfl, fun k h1 _ => by
    cases k with
    | zero => exact h
    | succ k => simp at h1⟩

theorem pw_two {x x' : Prog.Ev SKind BVal} {y y' : Prog.Ev AKind BVal} (h : EvRel Maps x y)
    (h' : EvRel Maps x' y') : PW (EvRel Maps) [x, x'] [y, y'] :=
  ⟨rfl, fun k h1 _ => by
    rcases k with _ | _ | k
    · exact h
    · exact h'
    · simp at h1; omega⟩

theorem sagrees_head {m : Memory} {e : Ev} {es : List Ev} (h : SAgrees m (e :: es))
    (hR : e.k.dir = .R) : readM e.n e.addr m = e.val :=
  h.1 hR

/-- **A read event at the access** against the CLIF read of the bytes the CLIF memory holds after
storing the read memory's bytes there. -/
theorem evrel_read {e : Ev} {M : Memory} {k : SKind} (hk : Maps k e.k) (hR : e.k.dir = .R)
    (hag : readM e.n e.addr M = e.val) {a n : Nat} (hA : e.addr = BitVec.ofNat 64 a)
    (hn : e.n = n) (ha : a < 2 ^ 64) (cm : Clif.Mem) :
    EvRel Maps ⟨k, .R, a, n,
      getB (cm.writeBits false a n (readM n (BitVec.ofNat 64 a) M)).bytes a n⟩
      (ProgE2E.convEv e) := by
  obtain ⟨h1, h2, h3⟩ := conv_at hag hA hn ha
  refine ⟨hk, by simp [ProgE2E.convEv, hR], h1, h2, ?_⟩
  rw [h3]
  show _ = getB (cm.writeBits false a n (readM n (BitVec.ofNat 64 a) M)).bytes a n
  rw [getB_writeBits, valB_false]

/-- **A write event at the access** against a CLIF write of its bytes. -/
theorem evrel_write {e : Ev} {k : SKind} (hk : Maps k e.k) (hW : e.k.dir = .W) {a n : Nat}
    (hA : e.addr = BitVec.ofNat 64 a) (hn : e.n = n) (ha : a < 2 ^ 64) {v : BVal}
    (hv : ProgE2E.bytesOf e.n e.val = v) : EvRel Maps ⟨k, .W, a, n, v⟩ (ProgE2E.convEv e) :=
  ⟨hk, by simp [ProgE2E.convEv, hW], loc_at hA ha, hn, hv⟩

/-- The memory after events ending with a write holds the write's bytes. -/
theorem applyW_last {es : List Ev} {wr : Ev} (hW : wr.k.dir = .W) {A : BitVec 64} {n : Nat}
    (hA : wr.addr = A) (hn : wr.n = n) (hn64 : n ≤ 2 ^ 64) (m : Memory) :
    ∀ k < n, applyW (es ++ [wr]) m (A + BitVec.ofNat 64 k) = wr.val.extractLsb' (8 * k) 8 := by
  obtain ⟨kk, addr, n', val⟩ := wr
  simp only at hW hA hn ⊢
  subst hA hn
  intro k hk
  rw [applyW_append]
  simp only [applyW, hW, ite_true]
  exact writeM_apply_in _ _ _ _ _ hn64 hk

/-- **The bytes of a VCode write at a CLIF access are the CLIF write's bytes** (`bytes_of_mr`). -/
theorem write_val {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (hMR : MemRelOk F sb syms f MR)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : ArmState} (hmr : MR sl cm w)
    {a n : Nat} (hv : cm.valid a n = true) {big : Bool} {wd : Nat} {v : BitVec wd}
    (hg : getB cm.bytes a n = valB big n v) {e : Ev} (ha : e.addr = BitVec.ofNat 64 a)
    (hn : e.n = n)
    (hmem : ∀ k < n, w.mem (e.addr + BitVec.ofNat 64 k) = e.val.extractLsb' (8 * k) 8) :
    ProgE2E.bytesOf e.n e.val = valB big n v := by
  rw [bytes_of_mr hMR hmr hv (getB_valB_some hg) ha hn hmem, hg]

theorem getB_putB_valB (B : Bytes) {w : Nat} (big : Bool) (a n : Nat) (v : BitVec w) :
    getB (putB B a n (valB big n v)) a n = valB big n v :=
  bytesI.get_put_same B a n _ (valB_length big n v)

/-- The memory instruction of an `atomic_rmw` (`casOkB`). -/
theorem rmw_form {op : Clif.AtomicRmwOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp x : Nat}
    {ms : List MInst} {mi : MInst} (h : casOkB (.atomicRmw op ty fl pp x) ms = true)
    (hm : mi ∈ ms) (hk : akinds mi ≠ []) :
    ∃ t op' fl' p x' d d1 d2, mi = .atomicRmwLoop t op' fl' (.vreg p .int) (.vreg x' .int)
      (.vreg d .int) (.vreg d1 .int) (.vreg d2 .int) := by
  have hmm : mi ∈ SegShape.memInsts ms := List.mem_filter.mpr ⟨hm, by
    cases hh : akinds mi with
    | nil => exact absurd hh hk
    | cons _ _ => rfl⟩
  have hP := List.all_eq_true.mp h mi hmm
  split at hP
  · simp only [Bool.and_eq_true] at hP
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hP
    obtain ⟨_, rfl⟩ := intV_eq h1
    obtain ⟨_, rfl⟩ := intV_eq h2
    obtain ⟨_, rfl⟩ := intV_eq h3
    obtain ⟨_, rfl⟩ := intV_eq h4
    obtain ⟨_, rfl⟩ := intV_eq h5
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  · cases hP

/-- The memory instruction of an `atomic_cas` (`casOkB`). -/
theorem cas_form {ty : Clif.Ty} {fl : Clif.MemFlags} {pp ex x : Nat}
    {ms : List MInst} {mi : MInst} (h : casOkB (.atomicCas ty fl pp ex x) ms = true)
    (hm : mi ∈ ms) (hk : akinds mi ≠ []) :
    ∃ t fl' p e x' d d1, mi = .atomicCasLoop t fl' (.vreg p .int) (.vreg e .int)
      (.vreg x' .int) (.vreg d .int) (.vreg d1 .int) := by
  have hmm : mi ∈ SegShape.memInsts ms := List.mem_filter.mpr ⟨hm, by
    cases hh : akinds mi with
    | nil => exact absurd hh hk
    | cons _ _ => rfl⟩
  have hP := List.all_eq_true.mp h mi hmm
  repeat' split at hP
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, rfl⟩
    | cases hP

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **The segment of a memory statement** (module doc), with progress, the return covered and the
VCode end off `rets` (`SegResRN`): where the thread's run ends inside the segment, the forward run
of the segment on the thread's own bytes (`stmt_matchN` on the CLIF state holding them,
`mr_own`) has a step there. On `DriverHypT` and the check admitting calls (#473), the statement
not a call. -/
theorem mem_segRTN (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) (hncall : ∀ fn args, stm.inst ≠ .call fn args)
    {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegResRN env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  -- the statement, its lowering and its code
  obtain ⟨hcall, hfunc, hslots, hmr, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := id hm
  simp only at hk hheld hcons hB hmr
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hchkS := stmtOk_ofC hchk hB hstm hL hsl hncall
  have hthr : threadInstB stm.inst = true := by
    simp only [stmtOkB, Bool.and_eq_true] at hchkS; exact hchkS.1.1.1
  obtain ⟨ks, nE, hexp⟩ : ∃ ks nE, SegShape.expect stm.inst = some (ks, nE) := by
    cases h : stm.inst <;> rw [h] at hthr hnp <;> simp [threadInstB, pureInst] at hthr hnp <;>
      exact ⟨_, _, rfl⟩
  obtain ⟨pre0, mi0, post0, hms, hpre0, hpost0, hks, hnE, hall, hcas⟩ := mem_split hchkS hexp
  have hsegat := seg_at hcode htne hjlt
  have hseg : seg f R bl b j =
      (pre0 ++ mi0 :: (post0 ++ extraOf stm.results sl.rss)).map (·.mapRegs R) := by
    rw [seg_eq hB hL hstm hsl, hms]; simp
  have hlen : (seg f R bl b j).length =
      pre0.length + 1 + (post0 ++ extraOf stm.results sl.rss).length := by
    rw [hseg]; simp; omega
  have hlt : k + (seg f R bl b j).length < vb.insts.size := by
    have := hsegat.2; rw [pos_succ] at this; rw [hk]; exact this
  have hat : ∀ i, i < (seg f R bl b j).length → vb.insts[k + i]? = (seg f R bl b j)[i]? :=
    fun i hi => by rw [hk, hsegat.1 i hi, List.getElem?_eq_getElem hi]
  have hall' : ∀ i ∈ pre0 ++ mi0 :: post0, instOkB i = true := fun i hi => hall i (hms ▸ hi)
  -- the thread walks to the memory instruction
  have hpos : ∀ i < pre0.length, ∃ ins, vb.insts[k + i]? = some ins ∧ akinds ins = [] ∧
      isRetsB ins = false := by
    intro i hi
    refine ⟨(pre0[i]).mapRegs R, ?_, ?_, ?_⟩
    · rw [hat i (by omega), hseg, List.map_append, List.getElem?_append_left (by simpa using hi)]
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem hi]; rfl
    · rw [SegShape.akinds_mapRegs]; exact hpre0 _ (List.getElem_mem _)
    · rw [isRetsB_mapRegs]
      exact notRets_of_instOkB (hall' _ (List.mem_append_left _ (List.getElem_mem _)))
  have hpost : ∀ i < (seg f R bl b j).length - (pre0.length + 1), ∃ ins,
      vb.insts[k + (pre0.length + 1) + i]? = some ins ∧ akinds ins = [] ∧ isRetsB ins = false := by
    intro i hi
    have hi' : i < (post0 ++ extraOf stm.results sl.rss).length := by rw [hlen] at hi; omega
    have hmem := List.getElem_mem hi'
    refine ⟨((post0 ++ extraOf stm.results sl.rss)[i]).mapRegs R, ?_, ?_, ?_⟩
    · rw [show k + (pre0.length + 1) + i = k + (pre0.length + 1 + i) by omega,
        hat _ (by rw [hlen]; omega), hseg, List.map_append,
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, show pre0.length + 1 + i - pre0.length = i + 1 by omega,
        List.map_cons, List.getElem?_cons_succ, List.getElem?_map]
      rw [List.getElem?_eq_getElem hi']; rfl
    · rw [SegShape.akinds_mapRegs]
      rcases List.mem_append.mp hmem with h | h
      · exact hpost0 _ h
      · exact (extra_facts h).1
    · rw [isRetsB_mapRegs]
      rcases List.mem_append.mp hmem with h | h
      · exact notRets_of_instOkB (hall' _ (by simp [h]))
      · exact (extra_facts h).2
  have hmidx : vb.insts[k + pre0.length]? = some (mi0.mapRegs R) := by
    rw [hat _ (by rw [hlen]; omega), hseg]; simp
  have hmL : pre0.length < (seg f R bl b j).length := by rw [hlen]; omega
  have hsegpre : SegAt vb k (pre0.map (·.mapRegs R)) := by
    intro i hi
    rw [hat i (by rw [hlen]; simp at hi; omega), hseg, List.map_append,
      List.getElem?_append_left (by simpa using hi), List.getElem?_eq_getElem hi]
  have hltpre : k + (pre0.map (·.mapRegs R)).length < vb.insts.size := by
    have := hlt; rw [hlen] at this; rw [List.length_map]; omega
  -- statements of the scope are no calls
  have hnc : ∀ fn args, stm.inst ≠ .call fn args := fun fn args h => by
    rw [h] at hthr; simp [threadInstB, pureInst] at hthr
  have hnci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args := fun _ _ _ h => by
    rw [h] at hthr; simp [threadInstB, pureInst] at hthr
  have hext : ∀ (s1 : Clif.State) fn args, stm.inst = .call fn args → ∀ e,
      s1.frame.func.extern? fn = some e → p.func? e.name = none :=
    fun _ fn args h => absurd h (hnc fn args)
  have hind : ∀ (s1 : Clif.State) sig callee args, stm.inst = .callIndirect sig callee args →
      ∀ cv, s1.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s1.mem.symbols g.name ≠ some cv.toNat :=
    fun _ sig callee args h => absurd h (hnci sig callee args)
  -- the CLIF statement steps on some bytes, or the CLIF thread has no step
  by_cases hnex : ¬ ∃ B0 s0, Clif.step env p (withBytes s B0) = .next s0
  · have hex := hnex
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl (done_of_all fun B => ?_)), fun _ h => by cases h⟩
    refine res_none_of (fun s' h => hex ⟨B, s', h⟩) (fun v m h => ?_)
    exact stmt_not_done (s := withBytes s B) hbody (hext _) (hind _) h
  obtain ⟨B0, s0, hs0⟩ := Classical.not_not.mp hnex
  have hs0' := hs0
  rw [step_stmt env p (withBytes s B0) stm rest hbody (hext _) (hind _)] at hs0'
  obtain ⟨vals0, m0, h0⟩ : ∃ vals0 m0,
      instOutcome env p s.frame (withB s.mem B0) stm.inst = .ok (vals0, m0) := by
    cases hO : instOutcome env p (withBytes s B0).frame (withBytes s B0).mem stm.inst with
    | ok r => exact ⟨r.1, r.2, hO⟩
    | trap c => rw [hO] at hs0'; cases hs0'
    | stuck m => rw [hO] at hs0'; cases hs0'
  have hrl : stm.results.length = vals0.length := by
    have h0' : instOutcome env p (withBytes s B0).frame (withBytes s B0).mem stm.inst =
        .ok (vals0, m0) := h0
    rw [h0'] at hs0'
    simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs0'
    cases hsm : (withBytes s B0).frame.regs.setMany stm.results vals0 with
    | none => rw [hsm] at hs0'; cases hs0'
    | some r => exact setMany_length hsm
  -- the forward run of the segment on the thread's own bytes, or an `atomic_cas` on read-only
  -- data
  have hpro : (∃ cL, StarN (VStep vc (csem F fc X)) (seg f R bl b j).length
      (.run ⟨b, k, ρ, w⟩) (.run cL)) ∨ CasRO (.run s) := by
    by_cases hfe : stm.inst = .fence
    · have hv0 : vals0 = [] := by
        rw [hfe] at h0; simp [instOutcome, Clif.evalInst] at h0; exact h0.1
      obtain ⟨s', hs, -⟩ := step_next_of (c := s.mem) hbody hnc hnci hs0 h0
        (by rw [hfe]; rfl) (by rw [hv0])
      have hs' : Clif.step env p s = .next s' := hs
      obtain ⟨B', j', ρL, wL, hB', hstm', hbd', -, hstar, -, -⟩ :=
        stmt_matchNT H hm hbody (hind s) (hext s) hs'
      rw [hB] at hB'; cases hB'
      have hjj : j' = j := by
        have e1 := congrArg List.length (hbd.symm.trans hbd')
        have := (List.getElem?_eq_some_iff.mp hstm').1
        simp at e1; omega
      subst hjj
      exact .inl ⟨_, hstar.toN⟩
    obtain ⟨a, n, hacc⟩ := access_of_ok hthr hnp hfe h0
    obtain ⟨hnEn, -⟩ := expect_access hexp hacc
    subst hnEn
    by_cases hro0 : isCas stm.inst = true ∧ s.mem.readonlyAt a nE = true
    · refine .inr ?_
      obtain ⟨hc, hro⟩ := hro0
      cases hi : stm.inst <;> rw [hi] at hc <;> simp [isCas] at hc
      exact ⟨s, stm, rest, _, _, _, _, _, a, nE, rfl, hbody, hi, hi ▸ hacc, hro⟩
    have hro : isCas stm.inst = true → s.mem.readonlyAt a nE = false := fun hc => by
      cases h : s.mem.readonlyAt a nE
      · rfl
      · exact absurd ⟨hc, h⟩ hro0
    have hfacts := mem_facts h0 hacc hro
    have hv : s.mem.valid a nE = true := by
      cases hs : isStore stm.inst
      · exact (hfacts.2 hs).1
      · exact (hfacts.1 hs).1
    obtain ⟨-, hlen0⟩ := outcome_shape hthr hnp hfe h0
    have hok_any : ∀ c : Clif.Mem, c.allocs = s.mem.allocs →
        (∀ j < nE, (c.bytes (a + j)).isSome) →
        ∃ vs c', instOutcome env p s.frame c stm.inst = .ok (vs, c') := by
      intro c hca hci
      cases hs : isStore stm.inst
      · obtain ⟨-, -, hall2, -⟩ := hfacts.2 hs
        obtain ⟨v, vs, c', he⟩ := hall2 c hca hci
        exact ⟨_, _, he⟩
      · obtain ⟨-, big, wd, v, hall2⟩ := hfacts.1 hs
        exact ⟨_, _, hall2 c hca⟩
    have hmr1 : MR slots (s.mem.writeBits false a nE (readM nE (BitVec.ofNat 64 a) w.mem)) w :=
      mr_own hMR hmr hv
    obtain ⟨vs1, cm1', h1o⟩ := hok_any (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) w.mem)) rfl (writeBits_isSome _ _ _ _ _)
    obtain ⟨-, hl1⟩ := outcome_shape hthr hnp hfe h1o
    obtain ⟨s1, hs1, -⟩ := step_next_of hbody hnc hnci hs0 h0 h1o (by rw [hl1, hlen0])
    obtain ⟨B', j', ρL, wL, hB', hstm', hbd', -, hstar, -, -⟩ :=
      stmt_matchNT H (match_mem (s2 := { s with mem := (s.mem.writeBits false a nE
        (readM nE (BitVec.ofNat 64 a) w.mem)) }) hm rfl rfl hmr1) hbody (hind _) (hext _) hs1
    rw [hB] at hB'; cases hB'
    have hjj : j' = j := by
      have e1 := congrArg List.length (hbd.symm.trans hbd')
      have := (List.getElem?_eq_some_iff.mp hstm').1
      simp at e1; omega
    subst hjj
    exact .inl ⟨_, hstar.toN⟩
  -- the walk
  rcases vtrun_walk (F := F) (ctx := fc) (X := X) hvb pre0.length hpos (by omega) hr with
    ⟨ρm, wm, pre, rest1, htr, hpl, hpe, h1, h2, hwm⟩ | ⟨hl, hpe⟩
  rotate_left
  · rcases hpro with ⟨cL, hstar1⟩ | hro
    · rcases vstep_of_vtrunR (retsRet_csem F fc X) hr hpe hstar1 (by omega) with
        ⟨hv, hnr⟩ | ⟨he, -⟩
      · exact .inl ⟨tr.length, [], .run s, Nat.le_refl _, .nil,
          (by rw [List.take_length]; exact corr_nil_tgts hpe), .inl ⟨rfl, hv, hnr⟩,
          fun _ h => by cases h⟩
      · omega
    · exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inr hro), fun _ h => by cases h⟩
  cases h2 with
  | nil =>
    subst htr
    rcases hpro with ⟨cL, hstar1⟩ | hro
    · rcases vstep_of_vtrunR (retsRet_csem F fc X) h1 hpe hstar1 (by omega) with
        ⟨hv, hnr⟩ | ⟨he, -⟩
      · exact .inl ⟨_, [], .run s, Nat.le_refl _, .nil,
          (by rw [List.take_length, List.append_nil]; exact corr_nil_tgts hpe),
          .inl ⟨rfl, hv, hnr⟩, fun _ h => by cases h⟩
      · omega
    · exact .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inr hro), fun _ h => by cases h⟩
  | @cons _ c'' _ evs rest2 hstep h3 =>
  subst htr
  -- the thread step at the memory instruction
  obtain ⟨vb', i', ops', hb', hi', hops', hev', hf', hst'⟩ := vtstep_evs hstep
  rw [hvb] at hb'; cases hb'
  rw [hmidx] at hi'; cases hi'
  by_cases hfe : stm.inst = .fence
  · ---------------------------------------------------------------- fence
    have hmi0 : mi0 = .fence := akinds_dmb (hks.trans (by
      rw [hfe] at hexp; simp [SegShape.expect] at hexp; exact hexp.1.symm))
    subst hmi0
    have hv0 : vals0 = [] := by
      rw [hfe] at h0; simp [instOutcome, Clif.evalInst] at h0; exact h0.1
    obtain ⟨s', hs, -⟩ := step_next_of (c := s.mem) hbody hnc hnci hs0 h0
      (by rw [hfe]; rfl) (by rw [hv0])
    have hs' : Clif.step env p s = .next s' := hs
    have hE : evs = [dmbEv] := by rw [hev']; exact IselMemAux.cEvs_fence F fc _ _
    subst hE
    obtain ⟨ρ'', w'', hc'', -⟩ := vtstep_next hvb hmidx (.inl rfl) hstep
    subst hc''
    obtain ⟨B', j', ρL, wL, hB', hstm', hbd', hk', hstar, -, hM⟩ :=
      stmt_matchNT H hm hbody (hind s) (hext s) hs'
    rw [hB] at hB'; cases hB'
    have hjj : j' = j := by
      have e1 := congrArg List.length (hbd.symm.trans hbd')
      have := (List.getElem?_eq_some_iff.mp hstm').1
      simp at e1; omega
    subst hjj
    have hpc : patchC [dmbEv] (.run ⟨b, k, ρ, w⟩) = .run ⟨b, k, ρ, w⟩ := rfl
    refine mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 (by rw [hpc]; exact hstar.toN) hM
      (ClifCStep.cstep_fence hbody hfe hs') (by simp) (pw_one ?_)
    simp [EvRel, Maps, ProgE2E.convEv, dmbEv, AKind.dir, ProgE2E.bytesOf]
  ---------------------------------------------------------------- the access
  obtain ⟨a, n, hacc⟩ := access_of_ok hthr hnp hfe h0
  obtain ⟨hnEn, hn0⟩ := expect_access hexp hacc
  subst hnEn
  have hn : SegShape.memBytes mi0 = some nE := by
    rcases hnE with h | h
    · exact absurd (expect_dmb hexp h) hfe
    · exact h
  by_cases hro0 : isCas stm.inst = true ∧ s.mem.readonlyAt a nE = true
  · refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inr ?_), fun _ h => by cases h⟩
    obtain ⟨hc, hro⟩ := hro0
    cases hi : stm.inst <;> rw [hi] at hc <;> simp [isCas] at hc
    exact ⟨s, stm, rest, _, _, _, _, _, a, nE, rfl, hbody, hi, hi ▸ hacc, hro⟩
  have hro : isCas stm.inst = true → s.mem.readonlyAt a nE = false := fun hc => by
    cases h : s.mem.readonlyAt a nE
    · rfl
    · exact absurd ⟨hc, h⟩ hro0
  have hfacts := mem_facts h0 hacc hro
  have hv : s.mem.valid a nE = true := by
    cases hs : isStore stm.inst
    · exact (hfacts.2 hs).1
    · exact (hfacts.1 hs).1
  obtain ⟨-, hlen0⟩ := outcome_shape hthr hnp hfe h0
  obtain ⟨ha64, -⟩ := hMR.valid _ _ _ a nE hmr hv
  have hok_any : ∀ c : Clif.Mem, c.allocs = s.mem.allocs → (∀ j < nE, (c.bytes (a + j)).isSome) →
      ∃ vs c', instOutcome env p s.frame c stm.inst = .ok (vs, c') := by
    intro c hca hci
    cases hs : isStore stm.inst
    · obtain ⟨-, -, hall2, -⟩ := hfacts.2 hs
      obtain ⟨v, vs, c', he⟩ := hall2 c hca hci
      exact ⟨_, _, he⟩
    · obtain ⟨-, big, wd, v, hall2⟩ := hfacts.1 hs
      exact ⟨_, _, hall2 c hca⟩
  have hres : isStore stm.inst = false → stm.results ≠ [] := by
    intro hs hnil
    rw [hs] at hlen0
    rw [hnil, List.length_nil] at hrl
    simp only [Bool.false_eq_true, ite_false] at hlen0
    omega
  -- the CLIF access holding the world's own bytes
  let cm1 := s.mem.writeBits false a nE (readM nE (BitVec.ofNat 64 a) w.mem)
  have hmr1 : MR slots cm1 w := mr_own hMR hmr hv
  obtain ⟨vs1, cm1', h1o⟩ := hok_any cm1 rfl (writeBits_isSome _ _ _ _ _)
  have hro1 : isCas stm.inst = true → cm1.readonlyAt a nE = false := fun hc =>
    (IselClif.readonlyAt_allocs rfl a nE).trans (hro hc)
  obtain ⟨ρb, wb, ops, hsrb, hops, hne, hAt, ⟨rc, hcs⟩, hwf, hem, halm, hextra, hcasx⟩ :=
    mem_vregT (s := { s with mem := cm1 }) H hMR hX hfunc hslots hmr1 hB hstm hheld hcons
      (hMRw _ _ _ hmr1).1 (hMRw _ _ _ hmr1).2 hL hsl hms hpre0 hpost0
      (fun i hi => covered_of_instOkB (hall' i hi)) hres (hms ▸ hcas) h1o hacc hro1 hn hn0
  have eops : ops' = ops := by rw [hops] at hops'; exact (Except.ok.inj hops').symm
  subst ops'
  -- the thread is where the code's run is
  have hdet : ρm = ρb ∧ wm = wb := by
    have hS1 := (vtrun_nil_starN h1 hpe w.mem).1
    have e1 : confMem w.mem (.run ⟨b, k, ρ, w⟩) = .run ⟨b, k, ρ, w⟩ :=
      confMem_self (.run ⟨b, k, ρ, w⟩)
    have e2 : confMem w.mem (.run ⟨b, k + pre0.length, ρm, wm⟩) =
        .run ⟨b, k + pre0.length, ρm, wm⟩ := by
      rw [← hwm]; exact confMem_self (.run ⟨b, k + pre0.length, ρm, wm⟩)
    rw [e1, e2, hpl] at hS1
    have hS2 := (seqRun_fall_starN hvb hsegpre hltpre hsrb).toN
    simp only [List.length_map] at hS2
    have e := vstepN_det hS1 hS2
    simp only [VConf.run.injEq, VState.mk.injEq] at e
    exact ⟨e.2.2.1, e.2.2.2⟩
  obtain ⟨rfl, rfl⟩ := hdet
  have hcsem : csem F fc X (mi0.mapRegs R) = csem F fc X mi0 := H.dsem.rename R gn H.shape.ren mi0
  have hev2 : evs = cEvs F fc mi0 (vuses ops ρm) (patch evs wm) :=
    hev'.trans (congrFun (congrFun (CEvsInv.cEvs_mapRegs H.shape.ren F fc mi0) _) _)
  have hst : mi0.isCtl = false → csemWF fc mi0 (vuses ops ρm) = true ∧ Arm.CheckSPAlignment wm :=
    fun hc => ⟨hwf hc, halm⟩
  have hEA : AtA (BitVec.ofNat 64 a) nE evs := by
    rw [hev2]; exact CEvsInv.cEvs_setMem_atA hem hst hcs hn _ hne hAt
  have hEne : evs ≠ [] := by
    intro he
    apply hne
    have h2 := hev2
    rw [he] at h2
    exact h2.symm
  obtain ⟨ρ'', w'', hc'', -⟩ := vtstep_next hvb hmidx
    (memBytes_form (by rw [SegShape.memBytes_mapRegs]; exact hn)) hstep
  subst hc''
  ------------------------------------------------ the CLIF access holding the bytes read
  have hn64 : nE ≤ 2 ^ 64 := by omega
  have ha : a < 2 ^ 64 := by omega
  have hMw : (patch evs wm).mem = applyR evs w.mem := by
    simp only [patch, setMem_mem, hwm]
  have hpw : patch evs w = write_mem_bytes nE (BitVec.ofNat 64 a)
      (readM nE (BitVec.ofNat 64 a) (patch evs wm).mem) w := by
    rw [patch_local hn64 hEA w, hMw]
  have hmr2 : MR slots (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch evs wm).mem)) (patch evs w) := by
    rw [hpw]; exact hMR.store slots s.mem w a nE _ hmr hv
  have hm2 := match_mem (s2 := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch evs wm).mem)) }) hm rfl rfl hmr2
  obtain ⟨vs2, cm2', h2o⟩ := hok_any (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch evs wm).mem)) rfl (writeBits_isSome _ _ _ _ _)
  obtain ⟨hal2, hl2⟩ := outcome_shape hthr hnp hfe h2o
  obtain ⟨s', hs2, hs'm⟩ := step_next_of hbody hnc hnci hs0 h0 h2o (by rw [hl2, hlen0])
  obtain ⟨B', j', ρL, wL, hB', hstm', hbd', hk', hstar, hsr, hM⟩ :=
    stmt_matchNT H hm2 hbody (hind _) (hext _) hs2
  rw [hB] at hB'; cases hB'
  have hjj : j' = j := by
    have e1 := congrArg List.length (hbd.symm.trans hbd')
    have := (List.getElem?_eq_some_iff.mp hstm').1
    simp at e1; omega
  subst j'
  ------------------------------------------------ the world after the segment
  have hseg' : seg f R bl b j =
      pre0.map (·.mapRegs R) ++ mi0.mapRegs R :: post0.map (·.mapRegs R) := by
    rw [hseg, hextra]; simp
  rw [hseg'] at hsr
  obtain ⟨ρ1, w1, hsr1, hsr2⟩ := seqRun_split hsr
  have hdet2 : ρm = ρ1 ∧ patch evs wm = w1 := by
    have hS1 := (vtrun_nil_starN h1 hpe (applyR evs w.mem)).1
    have e1 : confMem (applyR evs w.mem) (.run ⟨b, k, ρ, w⟩) = .run ⟨b, k, ρ, patch evs w⟩ := rfl
    have e2 : confMem (applyR evs w.mem) (.run ⟨b, k + pre0.length, ρm, wm⟩) =
        .run ⟨b, k + pre0.length, ρm, patch evs wm⟩ := by
      simp only [confMem, patch, hwm]
    rw [e1, e2, hpl] at hS1
    have hS2 := (seqRun_fall_starN hvb hsegpre hltpre hsr1).toN
    simp only [List.length_map] at hS2
    have e := vstepN_det hS1 hS2
    simp only [VConf.run.injEq, VState.mk.injEq] at e
    exact ⟨e.2.2.1, e.2.2.2⟩
  obtain ⟨rfl, rfl⟩ := hdet2
  obtain ⟨ops2, outs, w₁, hops2, hsem2, -, hrest⟩ := seqRun_cons_fall hsr2
  rw [hops'] at hops2; cases hops2
  have hw₁ : w₁.mem = applyW evs (patch evs wm).mem := by
    have e := hf'.2 (patch evs wm).mem hf'.1
    rw [setMem_self, hsem2] at e
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, hw, -⟩ := e
    rw [hw]; rfl
  have hcovm : SegFoot.Covered fc (mi0.mapRegs R) :=
    covered_of_instOkB (by rw [instOkB_mapRegs H.shape.ren]; exact hall' mi0 (by simp))
  have hep : Arm.r .ERR (patch evs wm) = .None := by rw [patch, err_setMem]; exact hem
  have halp : Arm.CheckSPAlignment (patch evs wm) := by rw [patch, spAlign_setMem]; exact halm
  obtain ⟨he₁, hal₁, -⟩ := SegFoot.csem_keep hcovm.1 hcovm.2.1
    (IselMemAux.covered_cov hcovm hops' ρm)
    hep halp hsem2
  have hpostc : ∀ i ∈ post0.map (·.mapRegs R), SegFoot.Covered fc i ∧ akinds i = [] := by
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    refine ⟨covered_of_instOkB (by
      rw [instOkB_mapRegs H.shape.ren]; exact hall' i0 (by simp [hi0])), ?_⟩
    rw [SegShape.akinds_mapRegs]; exact hpost0 _ hi0
  obtain ⟨hwL, -, -⟩ := seqRun_nomem hX hpostc he₁ hal₁ hrest
  have hmemW : ∀ (es : List Ev) (wr : Ev), evs = es ++ [wr] → wr.k.dir = .W →
      ∀ kk < nE, wL.mem (wr.addr + BitVec.ofNat 64 kk) = wr.val.extractLsb' (8 * kk) 8 := by
    intro es wr hes hW kk hkk
    obtain ⟨hA', hn'⟩ := hEA wr (by rw [hes]; simp)
    rw [hwL, hw₁, hes, hA']
    exact applyW_last hW hA' hn' hn64 _ kk hkk
  have hmrL : MR slots s'.mem wL := hM.2.2.2.1
  have hvL : s'.mem.valid a nE = true := valid_of_allocs (c := s.mem) (by rw [hs'm]; exact hal2) hv
  have hsub := VCodeEvents.cEvs_kinds F fc mi0 (vuses ops ρm) (patch evs wm)
  rw [← hev2, hks] at hsub
  have hcsem2 : csem F fc X mi0 (vuses ops ρm) (patch evs wm) = some (outs, w₁, .next) := by
    rw [← hcsem]; exact hsem2
  have hag0 : SAgrees (patch evs wm).mem evs := hf'.1
  have hmi0 : mi0 ∈ pre0 ++ mi0 :: post0 := by simp
  have hcas' := hms ▸ hcas
  ------------------------------------------------ per statement
  cases hi : stm.inst <;> rw [hi] at hthr hnp hfe hexp <;>
    simp only [threadInstB, pureInst, SegShape.expect, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq, Bool.false_eq_true] at hthr hnp hfe hexp
  case load op ty fl pp off =>
    obtain ⟨-, pv, hpv, hae⟩ := access_some_ite (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    rw [← hexp.1] at hsub
    obtain ⟨e, rfl, hek⟩ := single_of_sublist hsub hEne
    have hc2 := cstep_load (s := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch [e] wm).mem)) }) hbody hi hpv hs2
    rw [ea, en] at hc2
    have hR : e.k.dir = .R := by rw [hek]; rfl
    obtain ⟨hA, hn'⟩ := hEA e (by simp)
    exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
      (pw_one (evrel_read (by rw [hek]; rfl) hR (sagrees_head hag0 hR) hA hn' ha s.mem))
  case atomicLoad ty fl pp =>
    obtain ⟨-, pv, hpv, hae⟩ := access_some_ite (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    rw [← hexp.1] at hsub
    obtain ⟨e, rfl, hek⟩ := single_of_sublist hsub hEne
    have hc2 := cstep_atomicLoad (s := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch [e] wm).mem)) }) hbody hi hpv hs2
    rw [ea, en] at hc2
    have hR : e.k.dir = .R := by rw [hek]; rfl
    obtain ⟨hA, hn'⟩ := hEA e (by simp)
    exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
      (pw_one (evrel_read (by rw [hek]; exact .inl rfl) hR (sagrees_head hag0 hR) hA hn' ha s.mem))
  case store op ty fl x pp off =>
    obtain ⟨pv, hpv, hae⟩ := access_some (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    obtain ⟨v, pv', hv', hpv'⟩ := store_parts (hi ▸ h2o)
    rw [hpv] at hpv'; cases hpv'
    rw [← hexp.1] at hsub
    obtain ⟨e, rfl, hek⟩ := single_of_sublist hsub hEne
    have hc2 := cstep_store (s := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch [e] wm).mem)) }) hbody hi hpv hv' hs2
    have hown := cstep_own hc2 hs2 (by exact ⟨(fun h => nomatch h), trivial⟩)
    rw [applyEvs_write] at hown
    have hg : getB s'.mem.bytes a nE = valB (bigOf fl) nE v := by
      rw [hown, ← ea, ← en]; exact getB_putB_valB _ _ _ _ _
    rw [ea, en] at hc2
    have hW : e.k.dir = .W := by rw [hek]; rfl
    obtain ⟨hA, hn'⟩ := hEA e (by simp)
    have hval := write_val hMR hmrL hvL hg hA hn' (hmemW [] e rfl hW)
    exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
      (pw_one (evrel_write (by rw [hek]; rfl) hW hA hn' ha hval))
  case atomicStore ty fl x pp =>
    obtain ⟨pv, hpv, hae⟩ := access_some (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    obtain ⟨v, pv', hv', hpv'⟩ := atomicStore_parts (hi ▸ h2o)
    rw [hpv] at hpv'; cases hpv'
    rw [← hexp.1] at hsub
    obtain ⟨e, rfl, hek⟩ := single_of_sublist hsub hEne
    have hc2 := cstep_atomicStore (s := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch [e] wm).mem)) }) hbody hi hpv hv' hs2
    have hown := cstep_own hc2 hs2 (by exact ⟨(fun h => nomatch h), trivial⟩)
    rw [applyEvs_write] at hown
    have hg : getB s'.mem.bytes a nE = valB (bigOf fl) nE v := by
      rw [hown, ← ea, ← en]; exact getB_putB_valB _ _ _ _ _
    rw [ea, en] at hc2
    have hW : e.k.dir = .W := by rw [hek]; rfl
    obtain ⟨hA, hn'⟩ := hEA e (by simp)
    have hval := write_val hMR hmrL hvL hg hA hn' (hmemW [] e rfl hW)
    exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
      (pw_one (evrel_write (by rw [hek]; exact .inl rfl) hW hA hn' ha hval))
  case atomicRmw op ty fl pp x =>
    obtain ⟨-, pv, hpv, hae⟩ := access_some_ite (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    obtain ⟨pv', v, old, hpv', hv', hold⟩ := rmw_parts (hi ▸ h2o)
    rw [hpv] at hpv'; cases hpv'
    obtain ⟨t, op', fl', p0, x0, d0, d1, d2, rfl⟩ :=
      rmw_form (hi ▸ hcas') hmi0 (by rw [hks, ← hexp.1]; simp)
    have hu : vuses ops ρm = [ρm (gn p0), ρm (gn x0)] := by
      rw [operands_mapRegs H.shape.ren, operands_rmwLoop] at hops'
      cases hops'; simp [vuses, rnOp]; rfl
    rw [hu] at hcsem2 hev2
    obtain ⟨wr, hevs, hwk, -, -⟩ := IselMemAux.cEvs_rmw_shape hep hcsem2
    obtain ⟨r0, hevs', hrk⟩ : ∃ r0, evs = [r0, wr] ∧ r0.k = .acqXR := ⟨_, hev2.trans hevs, rfl⟩
    subst hevs'
    have hc2 := cstep_atomicRmw (s := { s with mem := (s.mem.writeBits false a nE
      (readM nE (BitVec.ofNat 64 a) (patch [r0, wr] wm).mem)) }) hbody hi hpv hv' hold hs2
    have hown := cstep_own hc2 hs2 (by exact ⟨fun _ => rfl, (fun h => nomatch h), trivial⟩)
    rw [applyEvs_rw] at hown
    have hg : getB s'.mem.bytes a nE = valB (bigOf fl) nE (Clif.Sem.atomicRmw op old v) := by
      rw [hown, ← ea, ← en]; exact getB_putB_valB _ _ _ _ _
    rw [ea, en] at hc2
    have hR : r0.k.dir = .R := by rw [hrk]; rfl
    have hW : wr.k.dir = .W := by rw [hwk]; rfl
    obtain ⟨hA, hn'⟩ := hEA r0 (by simp)
    obtain ⟨hAw, hnw⟩ := hEA wr (by simp)
    have hval := write_val hMR hmrL hvL hg hAw hnw (hmemW [r0] wr rfl hW)
    exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
      (pw_two (evrel_read (by rw [hrk]; exact .inr rfl) hR (sagrees_head hag0 hR) hA hn' ha s.mem)
        (evrel_write (by rw [hwk]; exact .inr rfl) hW hAw hnw ha hval))
  case atomicCas ty fl pp ex x =>
    obtain ⟨hle, pv, hpv, hae⟩ := access_some_ite (hi ▸ hacc)
    simp only [Prod.mk.injEq] at hae
    obtain ⟨ea, en⟩ := hae
    obtain ⟨pv', ev, v, old, hpv', hex, hx, hold⟩ := cas_parts (hi ▸ h2o)
    rw [hpv] at hpv'; cases hpv'
    obtain ⟨t, fl', p0, e0, x0, d0, d1, rfl⟩ :=
      cas_form (hi ▸ hcas') hmi0 (by rw [hks, ← hexp.1]; simp)
    obtain ⟨ua, uex, ux, hu, hh⟩ := hcasx ty fl pp ex x hi ev hex
    rw [hu] at hcsem2 hev2
    -- the comparisons of the statement and of the loop agree
    have hrd := (load_eq hle hold).2
    rw [ea, en] at hrd
    have hb : ∀ i < nE, ∀ y, (s.mem.writeBits false a nE
        (readM nE (BitVec.ofNat 64 a) (patch evs wm).mem)).bytes (a + i) = some y →
        Arm.read_mem (BitVec.ofNat 64 (a + i)) (patch evs w) = y := fun i hi' y hy =>
      hMR.bytes slots _ (patch evs w) (a + i) y hmr2 (valid_sub (valid_of_allocs rfl hv) hi') hy
    have hEA2 : AtA (BitVec.ofNat 64 a) nE
        (cEvs F fc (.atomicCasLoop t fl' (.vreg p0 .int) (.vreg e0 .int) (.vreg x0 .int)
          (.vreg d0 .int) (.vreg d1 .int)) [ua, uex, ux] (patch evs wm)) := by
      rw [← hev2]; exact hEA
    have hn8 : nE ≤ 8 := by
      have h2 := hEA2
      rcases IselMemAux.cEvs_cas_shape hep hcsem2 with ⟨hevs, -⟩ | ⟨wr, hevs, -⟩ <;>
      · rw [hevs] at h2
        have := (h2 _ List.mem_cons_self).2
        simp only at this
        rw [← this]
        have h := hcsem2
        simp only [csem, hep, ite_true] at h
        cases hL : loopSem F t ua (casLoopHead t.bits fl') [.x 25, .x 26, .x 28] [ua, uex, ux]
            [.x 27, .x 24] (patch evs wm) with
        | none => rw [hL] at h; cases h
        | some r1 => have := atomTy_bytes (loopSem_some hL).1; omega
    have hcmp := cas_cmp en hn8 hrd ha64 hb hh
    have hpm : (patch evs w).mem = (patch evs wm).mem := by rw [hMw]; rfl
    rw [hpm] at hcmp
    rcases IselMemAux.cEvs_cas_shape hep hcsem2 with ⟨hevs, hne'⟩ | ⟨wr, hevs, hwk, -, -, heq'⟩
    · -- the comparison fails: the read
      rw [hevs] at hEA2
      obtain ⟨hA0, hn0'⟩ := hEA2 _ List.mem_cons_self
      simp only at hA0 hn0'
      rw [hA0, hn0'] at hne'
      have hq : (old == ev) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hne' (hcmp.mp h)
      obtain ⟨r0, hevs', hrk⟩ : ∃ r0, evs = [r0] ∧ r0.k = .acqXR := ⟨_, hev2.trans hevs, rfl⟩
      subst hevs'
      have hc2 := cstep_atomicCas (s := { s with mem := (s.mem.writeBits false a nE
        (readM nE (BitVec.ofNat 64 a) (patch [r0] wm).mem)) }) hbody hi hpv hex hx hold hs2
      simp only [hq, Bool.false_eq_true, ite_false] at hc2
      rw [ea, en] at hc2
      have hR : r0.k.dir = .R := by rw [hrk]; rfl
      obtain ⟨hA, hn'⟩ := hEA r0 (by simp)
      exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
        (pw_one (evrel_read (by rw [hrk]; exact .inr rfl) hR (sagrees_head hag0 hR) hA hn' ha
          s.mem))
    · -- the comparison succeeds: the read and the write
      rw [hevs] at hEA2
      obtain ⟨hA0, hn0'⟩ := hEA2 _ List.mem_cons_self
      simp only at hA0 hn0'
      rw [hA0, hn0'] at heq'
      have hq : (old == ev) = true := by
        rw [beq_iff_eq]; exact hcmp.mpr heq'
      obtain ⟨r0, hevs', hrk⟩ : ∃ r0, evs = [r0, wr] ∧ r0.k = .acqXR := ⟨_, hev2.trans hevs, rfl⟩
      subst hevs'
      have hc2 := cstep_atomicCas (s := { s with mem := (s.mem.writeBits false a nE
        (readM nE (BitVec.ofNat 64 a) (patch [r0, wr] wm).mem)) }) hbody hi hpv hex hx hold hs2
      simp only [hq, ite_true] at hc2
      have hown := cstep_own hc2 hs2 (by exact ⟨fun _ => rfl, (fun h => nomatch h), trivial⟩)
      rw [applyEvs_rw] at hown
      have hg : getB s'.mem.bytes a nE = valB (bigOf fl) nE v := by
        rw [hown, ← ea, ← en]; exact getB_putB_valB _ _ _ _ _
      rw [ea, en] at hc2
      have hR : r0.k.dir = .R := by rw [hrk]; rfl
      have hW : wr.k.dir = .W := by rw [hwk]; rfl
      obtain ⟨hA, hn'⟩ := hEA r0 (by simp)
      obtain ⟨hAw, hnw⟩ := hEA wr (by simp)
      have hval := write_val hMR hmrL hvL hg hAw hnw (hmemW [r0] wr rfl hW)
      exact mem_completeRN hvb hmL hlt hpost hpl hpe h1 hstep h3 hstar.toN hM hc2 (by simp)
        (pw_two (evrel_read (by rw [hrk]; exact .inr rfl) hR (sagrees_head hag0 hR) hA hn' ha
          s.mem) (evrel_write (by rw [hwk]; exact .inr rfl) hW hAw hnw ha hval))
  case fence => exact absurd trivial hfe

/-- **The segment of a memory statement** (module doc), with progress and the return covered
(`SegResR`; `mem_segRTN`). -/
theorem mem_segRT (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) (hncall : ∀ fn args, stm.inst ≠ .call fn args)
    {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegResR env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT :=
  (mem_segRTN H hchk hMR hMRw hX hm hbody hnp hncall hr).toR

/-- **The segment of a memory statement** (module doc), with progress and the return covered
(`mem_segRT` on `DriverHyp` and `threadCheckBl`). -/
theorem mem_segR (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegResR env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  refine mem_segRT H.toT (threadCheckBlC_of hchk) hMR hMRw hX hm hbody hnp ?_ hr
  intro fn args h
  obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := hm
  obtain ⟨hjlt, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨-, -, hsllen, -⟩ := H.shape.blk _ B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have := stmtOk_of hchk hB hstm hL hsl
  simp [stmtOkB, threadInstB, h, pureInst] at this

/-- **The segment of a memory statement** (module doc), with progress (`SegResP`): where the
thread's run ends inside the segment, the forward run of the segment on the thread's own bytes
(`stmt_matchN` on the CLIF state holding them, `mr_own`) has a step there. -/
theorem mem_segP (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegResP env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT :=
  (mem_segR H hchk hMR hMRw hX hm hbody hnp hr).segResP

/-- **The segment of a memory statement** (module doc). -/
theorem mem_seg (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnp : pureInst stm.inst = false) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨b, k, ρ, w⟩) tr cT) :
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT :=
  (mem_segP H hchk hMR hMRw hX hm hbody hnp hr).segRes

end

end Concurrency.IselMemMain
