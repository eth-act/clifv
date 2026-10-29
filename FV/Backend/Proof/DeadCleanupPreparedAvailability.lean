import FV.Backend.Proof.DeadCleanupAvailability
import FV.Backend.Proof.DeadCleanupPrepareMap
import FV.Backend.Proof.KillPrep
import FV.Backend.Proof.SpillClasses

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Spill

def restrictedD (vc : VCode) (D : Nat → Nat → Bool) (b v : Nat) : Bool :=
  D b v && (exitLive vc 0 default).contains v

private theorem lookup {vc vcp : VCode} {b : Nat} {vb : VBlock}
    (hb : (preparedCleanup vc vcp).blocks[b]? = some vb) :
    ∃ old, vcp.blocks[b]? = some old ∧ vb = preparedCleanupBlock vc old := by
  rw [preparedCleanup_blocks, Array.getElem?_map] at hb
  obtain ⟨old, ho, he⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨old, ho, he.symm⟩

theorem preparedCleanup_entryStored (vc vcp : VCode) (ss ps : Array (Array Nat)) (s : Nat) :
    entryStored (preparedCleanup vc vcp) ss ps s = entryStored vcp ss ps s := by
  have hlookup (b : Nat) :
      (match (preparedCleanup vc vcp).blocks[b]?, ss[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) =
      (match vcp.blocks[b]?, ss[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) := by
    rw [preparedCleanup_blocks]
    simp only [Array.getElem?_map]
    cases hb : vcp.blocks[b]? with
    | none => rfl
    | some vb =>
      simp only [Option.map_some]
      cases ss[b]? with
      | none => rfl
      | some succ =>
        simp only
        cases hj : succ.toList.idxOf? s with
        | none => rfl
        | some j =>
          simp only [termEdgeDefs, (preparedCleanupBlock_interface vc vb).2.2.2]
  by_cases hex : ∃ b, ps[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hex
    rw [KillPrep.entryStored_one hp, KillPrep.entryStored_one hp]
    exact hlookup b
  · rw [KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩),
      KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩)]

private theorem block_ready {vc vcp : VCode} {ss ps : Array (Array Nat)}
    {D : Nat → Nat → Bool} (hav : SpillAvail vcp D) (hc : vcp.cfg = .ok (ss, ps))
    (hreads : ∀ vb ∈ vcp.blocks.toList, ∀ i ∈ vb.insts.toList,
      ∀ n ∈ uses vc.classes.size i, n ∈ exitLive vc 0 default)
    {b : Nat} {vb : VBlock} (hb : vcp.blocks[b]? = some vb) :
    AvailRunReady (preparedCleanupBlock vc vb).insts.toList
        (availStart (preparedCleanup vc vcp) ss ps (restrictedD vc D) b) ∧
      Agree (exitLive vc 0 default)
        (availAt vb.insts (availStart vcp ss ps D b) vb.insts.size)
        (availAt (preparedCleanupBlock vc vb).insts
          (availStart (preparedCleanup vc vcp) ss ps (restrictedD vc D) b)
          (preparedCleanupBlock vc vb).insts.size) := by
  obtain ⟨t, _, ht, hterm, _⟩ := (Prep.cfg_spec hc).blk b vb hb
  have hscan : (preparedCleanupBlock vc vb).insts =
      (scan vc.classes.size vb.insts.toList (exitLive vc 0 default)).1.toArray :=
    preparedCleanupBlock_insts vc ht hterm
  have hold : AvailRunReady vb.insts.toList (availStart vcp ss ps D b) := by
    apply (availRunReady_iff _ _).mpr
    intro k i ops hi hops o ho hu
    rw [Array.getElem?_toList] at hi
    exact hav.uses ss ps hc b vb k i ops hb hi hops o ho hu
  have hstart : Agree (scan vc.classes.size vb.insts.toList (exitLive vc 0 default)).2
      (availStart vcp ss ps D b)
      (availStart (preparedCleanup vc vcp) ss ps (restrictedD vc D) b) := by
    intro n hn
    have hnL := scan_boundary_subset
      (hreads vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))) n hn
    simp [availStart, restrictedD, hnL, preparedCleanup_entryStored]
  have h := scan_availability vc.classes.size vb.insts.toList (exitLive vc 0 default)
    _ _ hstart hold
  have hwhole : vb.insts.toList.take vb.insts.size = vb.insts.toList := by
    rw [← Array.length_toList, List.take_length]
  simpa only [hscan, availAt, List.toList_toArray, List.size_toArray, hwhole,
    List.take_length] using h

/-- Restrict the old availability sets to the pass's common boundary. The same
CFG delivers them, and every retained read remains available. -/
theorem preparedCleanup_spillAvail_of (vc vcp : VCode) (D : Nat → Nat → Bool)
    (hav : SpillAvail vcp D)
    (hreads : ∀ vb ∈ vcp.blocks.toList, ∀ i ∈ vb.insts.toList,
      ∀ n ∈ uses vc.classes.size i, n ∈ exitLive vc 0 default)
    (hargs : ∀ vb ∈ vcp.blocks.toList, ∀ a ∈ vb.branchArgs.toList,
      a.homeNum ∈ exitLive vc 0 default) :
    SpillAvail (preparedCleanup vc vcp) (restrictedD vc D) := by
  constructor
  · intro ss ps hc b vb k i ops hb hi hops o ho hu
    rw [preparedCleanup_cfg] at hc
    obtain ⟨old, hb0, rfl⟩ := lookup hb
    have hr := (block_ready hav hc hreads hb0).1
    exact (availRunReady_iff _ _).mp hr k i ops (by simpa using hi) hops o ho hu
  · intro ss ps hc b vb succ s sb hb hsucc hs hsb v hD
    rw [preparedCleanup_cfg] at hc
    obtain ⟨old, hb0, rfl⟩ := lookup hb
    obtain ⟨oldsb, hsb0, rfl⟩ := lookup hsb
    obtain ⟨hDold, hvL⟩ : D s v = true ∧ v ∈ exitLive vc 0 default := by
      simpa [restrictedD, Bool.and_eq_true] using hD
    have hold := hav.edges ss ps hc b old succ s oldsb hb0 hsucc hs hsb0 v hDold
    have hA := (block_ready hav hc hreads hb0).2
    simp only [edgeAvail, (preparedCleanupBlock_interface vc old).2.2.1,
      (preparedCleanupBlock_interface vc oldsb).2.1] at hold ⊢
    cases hi : (oldsb.params.toList.map Reg.homeNum).idxOf? v with
    | none =>
      simp only [hi] at hold ⊢
      rw [← hA v hvL]
      exact hold
    | some k =>
      simp only [hi] at hold ⊢
      cases ha : old.branchArgs[k]? with
      | none => simp [ha] at hold
      | some a =>
        simp only [ha] at hold ⊢
        have haL := hargs old (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb0)) a
          (Array.mem_toList_iff.mpr (Array.mem_of_getElem? ha))
        rw [← hA a.homeNum haL]
        exact hold

theorem restrictedD_entry_empty (vc : VCode) (D : Nat → Nat → Bool)
    (hD : ∀ v, D 0 v = false) : ∀ v, restrictedD vc D 0 v = false := by
  intro v
  simp [restrictedD, hD]

private theorem original_read (vc : VCode) {vb : VBlock} (hb : vb ∈ vc.blocks.toList)
    {i : MInst} (hi : i ∈ vb.insts.toList) {n : Nat} (hn : n ∈ uses vc.classes.size i) :
    n ∈ exitLive vc 0 default :=
  List.mem_flatMap.mpr ⟨vb, hb,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, hn⟩)⟩

theorem prepare_reads_boundary {vc vcp : VCode} (hd : Prep.PrepDomain vc)
    (hp : prepare vc = .ok vcp) :
    ∀ vb ∈ vcp.blocks.toList, ∀ i ∈ vb.insts.toList,
      ∀ n ∈ uses vc.classes.size i, n ∈ exitLive vc 0 default := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ :=
    Prep.prepare_facts hp
  intro vb hvb i hi n hn
  rcases Prep.insts3 hd (Prep.cfg_spec hc0) (Prep.cfg_spec hc2) hS hvb hi with
    ⟨raw, hraw, hi⟩ | ⟨raw, hraw, j, hj, ls, hset⟩ | ⟨l, rfl⟩
  · exact original_read vc hraw hi hn
  · have hu : uses vc.classes.size i = uses vc.classes.size j := by
      simp only [uses, (Driver.setTargets_facts hset).1]
    rw [hu] at hn
    exact original_read vc hraw hj hn
  · simp [uses, MInst.operands, MInst.visitOperands] at hn

theorem prepare_args_boundary {vc vcp : VCode} (hd : Prep.PrepDomain vc)
    (hcls : ClassesOkM vc) (hp : prepare vc = .ok vcp) :
    ∀ vb ∈ vcp.blocks.toList, ∀ a ∈ vb.branchArgs.toList,
      a.homeNum ∈ exitLive vc 0 default := by
  have rawargs : ∀ vb ∈ vc.blocks.toList, ∀ a ∈ vb.branchArgs.toList,
      a.homeNum ∈ exitLive vc 0 default := by
    intro vb hb a ha
    obtain ⟨n, c, rfl, _⟩ := hcls.2 vb hb a (List.mem_append_right _ ha)
    apply List.mem_flatMap.mpr
    refine ⟨vb, hb, List.mem_append_left _ ?_⟩
    simp only [regNums, Reg.homeNum, List.mem_filterMap]
    exact ⟨.vreg n c, ha, rfl⟩
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ :=
    Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨_, _, _, _, _, hR, _, _, _, _⟩ := Prep.facts_basic hd cs0 cs2 hS
  intro vb hvb a ha
  rw [Array.mem_toList_iff, Array.mem_map] at hvb
  obtain ⟨i, hiR, rfl⟩ := hvb
  have hi2 : i < (B ++ E).size := hR i (by simpa using hiR)
  rw [getElem!_pos (B ++ E) i hi2] at ha
  by_cases hiB : i < B.size
  · rw [Array.getElem_append_left hiB] at ha
    have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by
      rw [← hS.size]
      exact hiB
    obtain ⟨b, hb, e, _⟩ := Prep.keep_src hi1
    have hmem : (Prep.keep vc.blocks (reachable ss0))[i] ∈ vc.blocks.toList := by
      rw [e]
      simp
    obtain ⟨_, _, hba⟩ := Prep.rw_fields (hS.rw i hi1 hiB)
    rw [hba] at ha
    exact rawargs _ hmem a ha
  · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)] at ha
    have he : i - B.size < E.size := by simp at hi2; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [hl] at ha
    simp at ha

/-- The baseline availability hypothesis transports through preparation and
cleanup using the existing domain/classes facts of raw lowering. -/
theorem preparedCleanup_spillAvail {vc vcp : VCode} (hd : Prep.PrepDomain vc)
    (hcls : ClassesOkM vc) (hp : prepare vc = .ok vcp) (D : Nat → Nat → Bool)
    (hav : SpillAvail vcp D) :
    SpillAvail (preparedCleanup vc vcp) (restrictedD vc D) :=
  preparedCleanup_spillAvail_of vc vcp D hav
    (prepare_reads_boundary hd hp) (prepare_args_boundary hd hcls hp)

/-! Joint non-vacuity: real CFG, empty entry sets, actual deletion and all of
the read/edge premises used by the availability transport. -/
example : ∃ vc : VCode, (∃ ss ps, vc.cfg = .ok (ss, ps)) ∧
    SpillAvail vc (fun _ _ => false) ∧
    SpillAvail (preparedCleanup vc vc) (restrictedD vc (fun _ _ => false)) ∧
    (preparedCleanup vc vc).blocks[0]!.insts.toList = [.rets []] := by
  let m : MInst := .mov .size64 (.vreg 0 .int) .xzr
  let ret : MInst := .rets []
  let vb : VBlock := ⟨0, #[m, ret], #[], #[]⟩
  let vc : VCode := ⟨"availability_cleanup", #[vb], #[.int], 0, 0, #[]⟩
  have hm : m.operands = .ok #[⟨0, .int, .def, .late, .reg⟩] := rfl
  have hr : ret.operands = .ok #[] := rfl
  have hblock {b : Nat} {bb : VBlock} (hb : vc.blocks[b]? = some bb) : bb = vb := by
    have hi := (Array.getElem?_eq_some_iff.mp hb).1
    have hz : b = 0 := by simp [vc] at hi; omega
    subst b
    exact (Option.some.inj (show some vb = some bb by simpa [vc] using hb)).symm
  have hinst {i : MInst} {k : Nat} (hi : vb.insts[k]? = some i) : i = m ∨ i = ret := by
    have hin : i ∈ vb.insts.toList :=
      List.mem_iff_getElem?.mpr ⟨k, by simpa using hi⟩
    simpa [vb, or_comm, eq_comm] using hin
  have hav : SpillAvail vc (fun _ _ => false) := by
    constructor
    · intro ss ps hcfg b bb k i ops hb hi hop o ho hu
      have he := hblock hb
      subst bb
      rcases hinst hi with rfl | rfl
      · rw [hm] at hop
        cases hop
        simp at ho
        subst o
        cases hu
      · rw [hr] at hop
        cases hop
        simp at ho
    · intro ss ps hc b bb succ s sb hb hs hmem hsb v hd
      cases hd
  obtain ⟨ss, ps, hc⟩ : ∃ ss ps, vc.cfg = .ok (ss, ps) := Prep.cfg_of (by
    intro b bb hb
    rw [hblock hb]
    exact ⟨ret, rfl, rfl, fun _ h => by cases h⟩)
  refine ⟨vc, ⟨ss, ps, hc⟩, hav, ?_, ?_⟩
  · apply preparedCleanup_spillAvail_of vc vc _ hav
    · intro bb hb i hi v hv
      simp only [vc, List.mem_singleton] at hb
      subst bb
      simp only [vb, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp [uses, hm, hr] at hv
    · intro bb hb r harr
      simp only [vc, List.mem_singleton] at hb
      subst bb
      simp [vb] at harr
  · rw [preparedCleanup_blocks]
    simp only [vc, Array.map_singleton, getElem!_def, Array.getElem?_singleton, ite_true]
    rw [preparedCleanupBlock_insts vc (show vb.insts.back? = some ret from rfl) rfl]
    decide

end Backend.DeadCleanup
