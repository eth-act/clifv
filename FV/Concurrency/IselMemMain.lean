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

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

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
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  -- the statement, its lowering and its code
  obtain ⟨hcall, hfunc, hslots, hmr, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := id hm
  simp only at hk hheld hcons hB hmr
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hchkS := stmtOk_of hchk hB hstm hL hsl
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
    refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inl (done_of_all fun B => ?_))⟩
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
  -- the walk
  rcases vtrun_walk (F := F) (ctx := fc) (X := X) hvb pre0.length hpos (by omega) hr with
    ⟨ρm, wm, pre, rest1, htr, hpl, hpe, h1, h2, hwm⟩ | ⟨hl, hpe⟩
  rotate_left
  · exact .inl ⟨tr.length, [], .run s, Nat.le_refl _, .nil,
      (by rw [List.take_length]; exact corr_nil_tgts hpe), .inl rfl⟩
  cases h2 with
  | nil =>
    subst htr
    exact .inl ⟨_, [], .run s, Nat.le_refl _, .nil,
      (by rw [List.take_length, List.append_nil]; exact corr_nil_tgts hpe), .inl rfl⟩
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
      stmt_matchN H hm hbody (hind s) hs'
    rw [hB] at hB'; cases hB'
    have hjj : j' = j := by
      have e1 := congrArg List.length (hbd.symm.trans hbd')
      have := (List.getElem?_eq_some_iff.mp hstm').1
      simp at e1; omega
    subst hjj
    have hpc : patchC [dmbEv] (.run ⟨b, k, ρ, w⟩) = .run ⟨b, k, ρ, w⟩ := rfl
    refine mem_complete hvb hmL hlt hpost hpl hpe h1 hstep h3 (by rw [hpc]; exact hstar.toN) hM
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
  · refine .inl ⟨0, [], .run s, Nat.zero_le _, .nil, .nil, .inr (.inr ?_)⟩
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
    rw [hnil] at hrl
    simp at hlen0; omega
  -- the CLIF access holding the world's own bytes
  let cm1 := s.mem.writeBits false a nE (readM nE (BitVec.ofNat 64 a) w.mem)
  have hmr1 : MR slots cm1 w := mr_own hMR hmr hv
  obtain ⟨vs1, cm1', h1o⟩ := hok_any cm1 rfl (writeBits_isSome _ _ _ _ _)
  have hro1 : isCas stm.inst = true → cm1.readonlyAt a nE = false := fun hc =>
    (IselClif.readonlyAt_allocs rfl a nE).trans (hro hc)
  obtain ⟨ρb, wb, ops, hsrb, hops, hne, hAt, ⟨rc, hcs⟩, hwf, hem, halm, hextra, hcasx⟩ :=
    mem_vreg (s := { s with mem := cm1 }) H hMR hX hfunc hslots hmr1 hB hstm hheld hcons
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
  have hev2 : evs = cEvs F fc mi0 (vuses ops ρm) (patch evs wm) := by
    rw [hev', CEvsInv.cEvs_mapRegs H.shape.ren]
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
  sorry

end

end Concurrency.IselMemMain
