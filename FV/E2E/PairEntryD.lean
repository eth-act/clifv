import FV.E2E.PairEntry
import FV.E2E.PairGuardS

/-!
# The entry on paired worlds, reads guarded (SEM1 #537, #699)

`entry_step2P` (`PairEntry.lean`) with the paired run in the guarded paired semantics
`pairSemD` (`PairGuardS.lean`): the `Args` step is not a load form; each stack-argument load
reads bytes outside `F` that are equal on both worlds, so its reads avoid `F` and the difference
set (`csem_load` at that set). Same proofs. The pair guard does not depend on the semantics, so
the proofs are for any semantics with the memory forms (`entryLoads_runPDG`, `entry_step2PDGZ`,
whose runs stay in the entry code as the skip of unused instructions needs; `entry_step2PDG`; the
value semantics of the cleanup path uses them); the `csem` forms are their instances.

* `entryLoads_runPDG`, `entryLoads_runPD`;
* **`entry_step2PDGZ`**, **`entry_step2PDG`**, **`entry_step2PD`**.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E


section
variable {R : Reg → Reg} {sem : Sem}

/-- **The stack-argument loads on two worlds** with the same `x29` and the same argument bytes:
one paired run, whose projections are the two runs (any semantics with the memory forms). -/
theorem entryLoads_runPDG {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {ctx' : FnCtx} {X : ExtSem} (hMem : MemRefines F sb syms sem) :
    ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)) (ρ : Nat → CV) (w w' : Arm.ArmState),
      (∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int) →
      (E.map (·.1.1.1)).Nodup →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))) →
      Arm.r (.GPR 29#5) w' = Arm.r (.GPR 29#5) w →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → ∀ k < q.2,
        w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∃ ρ' w1 w1', seqRun (pairSemD sem F ctx' X) (E.filterMap (entryLoadOf R)) ρ (w, w') =
          some (.fall ρ' (w1, w1')) ∧
        seqRun sem (E.filterMap (entryLoadOf R)) ρ w = some (.fall ρ' w1) ∧
        seqRun sem (E.filterMap (entryLoadOf R)) ρ w' = some (.fall ρ' w1')
  | [], ρ, w, w', _, _, _, _, _ => ⟨ρ, w, w', rfl, rfl, rfl⟩
  | q :: E, ρ, w, w', hR, hnd, hst, h29, hby => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨⟨⟨x, ty⟩, loc⟩, b⟩ := q
    cases loc with
    | reg p =>
      exact entryLoads_runPDG hMem E ρ w w' (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2
        (fun q hq => hst q (List.mem_cons_of_mem _ hq)) h29
        (fun q hq => hby q (List.mem_cons_of_mem _ hq))
    | stack off =>
      obtain ⟨hb, hav⟩ := hst (((x, ty), ArgLoc.stack off), b) (List.mem_cons_self ..) off rfl
      obtain ⟨hob, hop, -⟩ := loadOpOfBytes_facts hb
      have ha : amodeAddr sb (.fpOffset (16 + (off : Int))) (loadOpOfBytes b).bytes [] w =
          some (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := rfl
      have ha' : amodeAddr sb (.fpOffset (16 + (off : Int))) (loadOpOfBytes b).bytes [] w' =
          some (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := by
        show some (Arm.r (.GPR 29#5) w' + _) = _
        rw [h29]
      obtain ⟨w1, hw1, hsw⟩ := hMem.1 (loadOpOfBytes b) x (.fpOffset (16 + (off : Int)))
        trustedFlags [] w _ hop ha (by rw [hob]; exact hav)
      obtain ⟨w1', hw1', hsw'⟩ := hMem.1 (loadOpOfBytes b) x (.fpOffset (16 + (off : Int)))
        trustedFlags [] w' _ hop ha' (by rw [hob]; exact hav)
      have hval : loadVal (loadOpOfBytes b) (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))
          w' = loadVal (loadOpOfBytes b) (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))
          w := by
        have hr : Arm.read_mem_bytes (loadOpOfBytes b).bytes
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w' =
            Arm.read_mem_bytes (loadOpOfBytes b).bytes
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w :=
          read_mem_bytes_congr _ _ (fun k hk => hby _ (List.mem_cons_self ..) off rfl k
            (by rw [hob] at hk; exact hk))
        simp only [loadVal, hr]
      rw [hval] at hw1'
      have hPD : ∀ {o : CV} {v1 v1' : Arm.ArmState},
          sem (.load (loadOpOfBytes b) (.vreg x .int) (.fpOffset (16 + (off : Int))) trustedFlags)
            [] w = some ([o], v1, .next) →
          sem (.load (loadOpOfBytes b) (.vreg x .int) (.fpOffset (16 + (off : Int))) trustedFlags)
            [] w' = some ([o], v1', .next) →
          pairSemD sem F ctx' X
            (.load (loadOpOfBytes b) (.vreg x .int) (.fpOffset (16 + (off : Int))) trustedFlags)
            [] (w, w') = some ([o], (v1, v1'), .next) := by
        intro o v1 v1' h1 h2
        have hY : Avoids (fun a => F a ∨ w.mem a ≠ w'.mem a) (loadOpOfBytes b).bytes
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := by
          intro k hk h
          rw [hob] at hk
          rcases h with h | h
          · exact hav k hk h
          · exact h (hby _ (List.mem_cons_self ..) off rfl k hk).symm
        have hG : PGuard F ctx' X
            (.load (loadOpOfBytes b) (.vreg x .int) (.fpOffset (16 + (off : Int))) trustedFlags) []
            (w, w') := by
          refine ⟨fun a => F a ∨ w.mem a ≠ w'.mem a, fun a h => .inl h, fun a h => .inr h,
            .inl ?_, .inl ?_⟩
          · obtain ⟨_, h, -⟩ := csem_load _ ctx' X _ hop x (.fpOffset (16 + (off : Int)))
              trustedFlags [] w _ rfl hY
            exact ⟨_, h⟩
          · obtain ⟨_, h, -⟩ := csem_load _ ctx' X _ hop x (.fpOffset (16 + (off : Int)))
              trustedFlags [] w' _ (show some (Arm.r (.GPR 29#5) w' + _) = _ by rw [h29]) hY
            exact ⟨_, h⟩
        rw [pairSemD_of hG]
        exact pairSem_eq h1 h2
      have h29a : Arm.r (.GPR 29#5) w1 = Arm.r (.GPR 29#5) w := hsw.1 (.GPR 29#5) (by simp [Masked])
      have h29b : Arm.r (.GPR 29#5) w1' = Arm.r (.GPR 29#5) w' :=
        hsw'.1 (.GPR 29#5) (by simp [Masked])
      have hst1 : ∀ q ∈ E, ∀ o, q.1.2 = .stack o → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
          Avoids F q.2 (Arm.r (.GPR 29#5) w1 + BitVec.ofInt 64 (16 + (o : Int))) := fun q hq o ho => by
        rw [h29a]; exact hst q (List.mem_cons_of_mem _ hq) o ho
      obtain ⟨ρ', v1, v1', hP, hA, hB⟩ := entryLoads_runPDG hMem E
        (upd ρ x (ofX (loadVal (loadOpOfBytes b)
          (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w)))
        w1 w1' (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2 hst1
        (by rw [h29b, h29, h29a])
        (fun q hq o ho k hk => by
          obtain ⟨-, hav'⟩ := hst q (List.mem_cons_of_mem _ hq) o ho
          have hnf := hav' k hk
          rw [h29a]
          rw [hsw'.2.1 _ hnf, hsw.2.1 _ hnf]
          exact hby q (List.mem_cons_of_mem _ hq) o ho k hk)
      have hRx : R (.vreg x .int) = .vreg x .int := hR _ (List.mem_cons_self ..)
      refine ⟨ρ', v1, v1', ?_, ?_, ?_⟩
      · simp only [List.filterMap_cons, entryLoadOf, hRx]
        rw [seqRun_load_consW (hPD hw1 hw1'), hP]; rfl
      · simp only [List.filterMap_cons, entryLoadOf, hRx]
        rw [seqRun_load_consW hw1, hA]; rfl
      · simp only [List.filterMap_cons, entryLoadOf, hRx]
        rw [seqRun_load_consW hw1', hB]; rfl

/-- **The stack-argument loads on two worlds** with the same `x29` and the same argument bytes:
one paired run, whose projections are the two runs. -/
theorem entryLoads_runPD {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {ctx' : FnCtx} {X : ExtSem} (hMem : MemRefines F sb syms sem) (_hs : sem = csem F ctx' X) :
    ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)) (ρ : Nat → CV) (w w' : Arm.ArmState),
      (∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int) →
      (E.map (·.1.1.1)).Nodup →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))) →
      Arm.r (.GPR 29#5) w' = Arm.r (.GPR 29#5) w →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → ∀ k < q.2,
        w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∃ ρ' w1 w1', seqRun (pairSemD sem F ctx' X) (E.filterMap (entryLoadOf R)) ρ (w, w') =
          some (.fall ρ' (w1, w1')) ∧
        seqRun sem (E.filterMap (entryLoadOf R)) ρ w = some (.fall ρ' w1) ∧
        seqRun sem (E.filterMap (entryLoadOf R)) ρ w' = some (.fall ρ' w1') :=
  entryLoads_runPDG hMem

end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **`entry_step2P` with the paired run guarded** (its proof), for any semantics with the memory
forms; the three runs in the entry code (`AtSeg 0 0 k`, as `entry_step2Z`). -/
theorem entry_step2PDGZ (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR) {ctx' : FnCtx} {X : ExtSem}
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ w₀' : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hmr' : MR slots cs.mem w₀') (hargs : ArgsAtEntry F f.sig args w₀)
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) :
    ∃ k ρ₁ w₁ w₁', StarP (VStep vc sem) (AtSeg 0 0 k) (.run ⟨0, 0, ρ₀, w₀⟩)
        (.run ⟨0, k, ρ₁, w₁⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ ∧ SameWorld F w₁ w₀ ∧
      StarP (VStep vc sem) (AtSeg 0 0 k) (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, k, ρ₁, w₁'⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁'⟩ ∧ SameWorld F w₁' w₀' ∧
      StarP (VStep vc (pairSemD sem F ctx' X)) (AtSeg 0 0 k) (.run ⟨0, 0, ρ₀, (w₀, w₀')⟩)
        (.run ⟨0, k, ρ₁, (w₁, w₁')⟩) := by
  obtain ⟨L, hL⟩ := H.blow hB0
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk 0 B0 L hB0 hL
  obtain ⟨hnd, hA⟩ := H.cert.entry B0 hB0
  have hB0mem : B0 ∈ f.blocks := List.mem_of_getElem? hB0
  obtain ⟨hlocs, bytes, hb⟩ := H.entryLocs
  have hbm := sigParamBytes_eq_map hb
  have hla : args.length = B0.params.length := by
    have := congrArg List.length hty; simpa using this
  have hls : args.length = f.sig.params.length := by
    have := congrArg List.length hsig; simpa using this
  have hlb : bytes.length = f.sig.params.length := by rw [hbm, List.length_map]
  obtain ⟨E, hEdef⟩ : ∃ E, E = entryParams f B0 := ⟨_, rfl⟩
  have hE : E = (B0.params.zip (locsOf f.sig)).zip bytes := by
    rw [hEdef]; simp only [entryParams, hb]
  have hEids : E.map (·.1.1.1) = B0.params.map (·.1) := by
    rw [hE]
    have h1 : (B0.params.zip (locsOf f.sig)).length = B0.params.length := by
      simp [List.length_zip]; omega
    have h2 : ((B0.params.zip (locsOf f.sig)).zip bytes).map Prod.fst =
        B0.params.zip (locsOf f.sig) := List.map_fst_zip (by omega)
    have h3 : (B0.params.zip (locsOf f.sig)).map Prod.fst = B0.params :=
      List.map_fst_zip (by omega)
    rw [show (fun q : ((Nat × Clif.Ty) × ArgLoc) × Nat => q.1.1.1) =
      (fun q : Nat × Clif.Ty => q.1) ∘ Prod.fst ∘ Prod.fst from rfl, ← List.map_map,
      ← List.map_map, h2, h3]
  have hRid : ∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int := by
    intro q hq
    have hq1 : q.1.1 ∈ B0.params := by
      rw [hE] at hq
      exact (List.of_mem_zip (List.of_mem_zip hq).1).1
    simp [H.shape.ren.vreg, H.shape.params B0 hB0mem q.1.1 hq1]
  have hEget : ∀ (m : Nat) (q : Clif.ValueId × Clif.Ty), B0.params[m]? = some q →
      ∃ (loc : ArgLoc) (b : Nat), (locsOf f.sig)[m]? = some loc ∧
      bytes[m]? = some b ∧ E[m]? = some ((q, loc), b) := by
    intro m q hq
    have hm : m < B0.params.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨loc, hloc⟩ : ∃ loc, (locsOf f.sig)[m]? = some loc :=
      ⟨(locsOf f.sig)[m]'(by omega), by simp⟩
    obtain ⟨b, hbb⟩ : ∃ b, bytes[m]? = some b := ⟨bytes[m]'(by omega), by simp⟩
    exact ⟨loc, b, hloc, hbb, by rw [hE]; simp [List.getElem?_zip_eq_some, hq, hloc, hbb]⟩
  have hbyte : ∀ (m : Nat) (v : Clif.Val) (b : Nat), args[m]? = some v → bytes[m]? = some b → b = v.ty.bytes := by
    intro m v b hv hbb
    rw [hbm, List.getElem?_map] at hbb
    have := congrArg (·[m]?) hsig
    simp only [List.getElem?_map, hv, Option.map_some] at this
    cases hp : f.sig.params[m]? with
    | none => rw [hp] at this; cases this
    | some p =>
      rw [hp] at this hbb
      simp only [Option.map_some, Option.some.injEq] at this hbb
      rw [← hbb, this]
  have hEmem : ∀ q ∈ E, ∃ (m : Nat) (v : Clif.Val), E[m]? = some q ∧ args[m]? = some v := by
    intro q hq
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hq
    have hmE : m < E.length := (List.getElem?_eq_some_iff.mp hm).1
    have : E.length ≤ args.length := by rw [hE]; simp [List.length_zip]; omega
    exact ⟨m, args[m]'(by omega), hm, by simp⟩
  have hentry : ∀ q ∈ E, ∀ (m : Nat) (v : Clif.Val), E[m]? = some q → args[m]? = some v →
      (q.1.2, v) ∈ (locsOf f.sig).zip args ∧ q.2 = v.ty.bytes ∧ bytes[m]? = some q.2 := by
    intro q hq m v hm hv
    rw [hE] at hm
    simp only [List.getElem?_zip_eq_some] at hm
    obtain ⟨⟨-, hl⟩, hbb⟩ := hm
    exact ⟨List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hl, hv]⟩,
      hbyte m v _ hv hbb, hbb⟩
  obtain ⟨ns, hnsdef⟩ : ∃ ns, ns = entryNs E := ⟨_, rfl⟩
  have hpre : pre f R 0 = .args (argPairs ns) :: E.filterMap (entryLoadOf R) := by
    simp only [pre, hB0, entryRegs, entryLoads, ← hEdef]
    rw [entryRegs_eq E hRid, ← hnsdef]
  have hnsnd : (ns.map (·.1)).Nodup := by
    rw [hnsdef]
    exact (entryNs_sublist E).nodup (by rw [hEids]; exact hnd)
  have hops := operands_args ns
  have hvu : vuses (argOps ns).toArray ρ₀ = [] := by
    simp only [vuses, List.toList_toArray, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; simp [Operand.isUse]
  -- the argument registers agree
  have hargsEq : (argPairs ns).map (fun d => regVal w₀' d.2) =
      (argPairs ns).map (fun d => regVal w₀ d.2) := by
    apply List.map_congr_left
    intro d hd
    obtain ⟨⟨x, p⟩, hxp, rfl⟩ := List.mem_map.mp hd
    rw [hnsdef] at hxp
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hxp
    obtain ⟨m, v, hm, hv⟩ := hEmem q hq
    obtain ⟨hmem, -, -⟩ := hentry q hq m v hm hv
    revert hqe hmem
    cases hl : q.1.2 with
    | stack o => intro hqe; cases hqe
    | reg r =>
      intro hqe hmem
      simp only [Option.some.injEq, Prod.mk.injEq] at hqe
      obtain ⟨-, rfl⟩ := hqe
      exact hreg r v hmem
  have hsem := hds.args (argPairs ns) w₀
  rw [← hvu] at hsem
  have hsem' := hds.args (argPairs ns) w₀'
  rw [← hvu, hargsEq] at hsem'
  have hlen : ((argPairs ns).map fun d => regVal w₀ d.2).length =
      ((argOps ns).toArray.toList.filter Operand.isDef).length := by
    have : (argOps ns).filter Operand.isDef = argOps ns := by
      rw [List.filter_eq_self]
      intro o ho
      obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
      rw [← hq']; rfl
    rw [List.toList_toArray, this]
    simp only [List.length_map, argPairs, argOps]
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁, ρ₁ = vdefUpd (argOps ns).toArray ((argPairs ns).map fun d => regVal w₀ d.2) ρ₀ :=
    ⟨_, rfl⟩
  have hloadsF : ∀ (w : Arm.ArmState), Arm.r (.GPR 29#5) w = Arm.r (.GPR 29#5) w₀ →
      ∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := by
    intro w hw q hq off ho
    obtain ⟨m, v, hm, hv⟩ := hEmem q hq
    obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
    have h := hargs _ _ hmem
    rw [ho] at h
    obtain ⟨hav, -⟩ := h
    rw [hqb, hw]
    exact ⟨hqb ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm), hav⟩
  obtain ⟨ρ₂, w₂, hrun, hmr₂, hfr, hreg2, hstk2, hsw2⟩ := entryLoads_run hMem hMR E ρ₁ slots
    cs.mem w₀ hRid (by rw [hEids]; exact hnd) (hloadsF w₀ rfl) hmr
  obtain ⟨ρ₂', w₂', hrun', hmr₂', hfr', hreg2', hstk2', hsw2'⟩ := entryLoads_run hMem hMR E ρ₁
    slots cs.mem w₀' hRid (by rw [hEids]; exact hnd) (hloadsF w₀' h29) hmr'
  have hρ₂ : ρ₂' = ρ₂ := by
    funext y
    by_cases hy : y ∈ E.map (·.1.1.1)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      cases hl : q.1.2 with
      | reg p => rw [hreg2' q hq p hl, hreg2 q hq p hl]
      | stack off =>
        rw [hstk2' q hq off hl, hstk2 q hq off hl, h29]
        obtain ⟨m, v, hm, hv⟩ := hEmem q hq
        obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
        have hbs : q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8 :=
          sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm)
        congr 1
        unfold loadVal
        rw [show Arm.read_mem_bytes (loadOpOfBytes q.2).bytes
            (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int))) w₀' =
            Arm.read_mem_bytes (loadOpOfBytes q.2).bytes
            (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int))) w₀ from
          read_mem_bytes_congr _ _ (fun k hk => by
            rw [(loadOpOfBytes_facts hbs).1, hqb] at hk
            exact hstk off v (hl ▸ hmem) k hk)]
    · rw [hfr' y hy, hfr y hy]
  rw [hρ₂] at hrun'
  obtain ⟨ρP, wP, wP', hrunP, hrunA, hrunB⟩ := entryLoads_runPDG (ctx' := ctx') (X := X) hMem E ρ₁
    w₀ w₀' hRid
    (by rw [hEids]; exact hnd) (hloadsF w₀ rfl) h29 (fun q hq off ho k hk => by
      obtain ⟨m, v, hm, hv⟩ := hEmem q hq
      obtain ⟨hmem, hqb, -⟩ := hentry q hq m v hm hv
      exact hstk off v (ho ▸ hmem) k (hqb ▸ hk))
  rw [hrun] at hrunA
  rw [hrun'] at hrunB
  simp only [Option.some.injEq, SeqEnd.fall.injEq] at hrunA hrunB
  obtain ⟨rfl, rfl⟩ := hrunA
  obtain ⟨-, rfl⟩ := hrunB
  have hsz : (pre f R 0).length < vb.insts.size := by
    have h1 : vb.insts.size = vb.insts.toList.length := by simp
    have h2 : 0 < (tseg R bl 0).length := List.length_pos_iff.mpr htne
    rw [h1, hcode]; simp only [List.length_append]; omega
  have hseg0 : SegAt vb 0 (pre f R 0) := by
    intro k hk
    rw [Nat.zero_add, ← Array.getElem?_toList, hcode, List.append_assoc,
      List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  have hvb0 : vb.insts[0]? = some (.args (argPairs ns)) := by
    exact SegAt.head (show SegAt vb 0 (MInst.args (argPairs ns) :: E.filterMap (entryLoadOf R)) by
      rw [← hpre]; exact hseg0)
  have hnext : 0 + 1 < vb.insts.size := by rw [hpre] at hsz; simp at hsz; omega
  have hstep : VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem hlen (VNext.next hnext)
  have hstep' : VStep vc sem (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, 1, ρ₁, w₀'⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem' hlen (VNext.next hnext)
  have hstepP : VStep vc (pairSemD sem F ctx' X) (.run ⟨0, 0, ρ₀, (w₀, w₀')⟩)
      (.run ⟨0, 1, ρ₁, (w₀, w₀')⟩) := by
    rw [hρ₁]
    refine VStep.step hvb hvb0 hops ?_ hlen (VNext.next hnext)
    rw [pairSemD_of (pGuard_noLoad rfl _ _)]
    exact pairSem_eq hsem hsem'
  have hseg1 : SegAt vb 1 (E.filterMap (entryLoadOf R)) := by
    have := (show SegAt vb 0 (.args (argPairs ns) :: E.filterMap (entryLoadOf R)) by
      rw [← hpre]; exact hseg0).tail
    simpa using this
  have hlt : 1 + (E.filterMap (entryLoadOf R)).length < vb.insts.size := by
    rw [hpre] at hsz; simp at hsz; omega
  have hstar := seqRun_fall_starP hvb hseg1 hlt hrun
  have hstar' := seqRun_fall_starP hvb hseg1 hlt hrun'
  have hstarP := seqRun_fall_starP hvb hseg1 hlt hrunP
  -- the vreg file holds the parameters, the DFG facts
  have hheld : Held gn (A 0 0) ρ₂ cs.frame := by
    intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hxp
    have hm' : m < B0.params.length := by simpa using hm
    have hqm : B0.params[m]? = some B0.params[m] := List.getElem?_eq_getElem hm'
    have hxq : B0.params[m].1 = x := by simpa using hxm
    have hma : m < args.length := by omega
    have hrx : cs.frame.regs x = some args[m] :=
      setMany_nodup hregs hnd m x args[m] (by rw [← hxq]; simp [hqm]) (List.getElem?_eq_getElem hma)
    refine ⟨args[m], hrx, ?_⟩
    have hgx : gn x = x := by
      rw [← hxq]; exact H.shape.params B0 hB0mem _ (List.getElem_mem hm')
    show VHolds args[m] (ρ₂ (gn x))
    rw [hgx]
    obtain ⟨loc, b, hloc, hbb, hEm⟩ := hEget m _ hqm
    have hqE : ((B0.params[m], loc), b) ∈ E := List.mem_of_getElem? hEm
    have hmem : (loc, args[m]) ∈ (locsOf f.sig).zip args :=
      List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hloc, hma]⟩
    have hb' : b = args[m].ty.bytes := hbyte m _ b (List.getElem?_eq_getElem hma) hbb
    have h := hargs _ _ hmem
    cases loc with
    | reg r =>
      have h1 := hreg2 _ hqE r rfl
      simp only at h1
      rw [← hxq, h1]
      have hns : (B0.params[m].1, r) ∈ ns := hnsdef ▸ mem_entryNs hqE rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hns
      rw [hρ₁, vdefUpd_argOps hnsnd (by simp [argPairs]) i hi (x := regVal w₀ r) (by simp [argPairs, hi])]
      exact h
    | stack off =>
      have h1 := hstk2 _ hqE off rfl
      simp only at h1
      rw [← hxq, h1, hb']
      obtain ⟨-, hrd⟩ := h
      have hbs : args[m].ty.bytes = 1 ∨ args[m].ty.bytes = 2 ∨ args[m].ty.bytes = 4 ∨
          args[m].ty.bytes = 8 := hb' ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hbb)
      obtain ⟨hob, -, hsg⟩ := loadOpOfBytes_facts hbs
      have hw : args[m].ty.width ≤ 64 :=
        (show ∀ t : Clif.Ty, (t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8) →
          t.width ≤ 64 by intro t; cases t <;> decide) _ hbs
      simp only [VHolds, ofX, loadVal, hsg, Bool.false_eq_true, ↓reduceIte]
      rw [hob, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]
      exact hrd
  have hdfg : DFGCons ctx (restrict cs.frame (A 0 0)) := by
    refine ⟨fun x d info cl v hd _ _ _ hv => ?_, fun x t v ht hv => ?_⟩
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [(hA x hx0).2] at hd
      cases hd
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [restrict_regs_of_mem hx0] at hv
      obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hregs hnd hty (hA x hx0).1 hv
      rw [H.cert.paramTy B0 hB0mem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
  have hmono : ∀ {W : Type} (c : VConf CV W),
      AtSeg 0 1 (E.filterMap (entryLoadOf R)).length c →
      AtSeg 0 0 (1 + (E.filterMap (entryLoadOf R)).length) c := by
    rintro W c ⟨i, hi, ρ', w', rfl⟩
    exact ⟨i + 1, by omega, ρ', w', by rw [Nat.zero_add, Nat.add_comm]⟩
  refine ⟨1 + (E.filterMap (entryLoadOf R)).length, ρ₂, w₂, w₂',
    .step (AtSeg.zero _ _ _ (by omega) _ _) hstep (hstar.mono fun c h => hmono c h),
    ⟨hcall, hfunc, hslots, hmr₂, B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
      by simp [pos, hpre]; omega, hheld, hdfg⟩, hsw2,
    .step (AtSeg.zero _ _ _ (by omega) _ _) hstep' (hstar'.mono fun c h => hmono c h),
    ⟨hcall, hfunc, hslots, hmr₂', B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
      by simp [pos, hpre]; omega, hheld, hdfg⟩, hsw2',
    .step (AtSeg.zero _ _ _ (by omega) _ _) hstepP (hstarP.mono fun c h => hmono c h)⟩

/-- **`entry_step2P` with the paired run guarded**, for any semantics with the memory forms
(`entry_step2PDGZ` as plain runs). -/
theorem entry_step2PDG (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR) {ctx' : FnCtx} {X : ExtSem}
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ w₀' : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hmr' : MR slots cs.mem w₀') (hargs : ArgsAtEntry F f.sig args w₀)
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) :
    ∃ k ρ₁ w₁ w₁', Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, k, ρ₁, w₁⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ ∧ SameWorld F w₁ w₀ ∧
      Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, k, ρ₁, w₁'⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁'⟩ ∧ SameWorld F w₁' w₀' ∧
      Star (VStep vc (pairSemD sem F ctx' X)) (.run ⟨0, 0, ρ₀, (w₀, w₀')⟩)
        (.run ⟨0, k, ρ₁, (w₁, w₁')⟩) :=
  let ⟨k, ρ₁, w₁, w₁', h1, h2, h3, h4, h5, h6, h7⟩ := entry_step2PDGZ H hds hMem hMR
    (ctx' := ctx') (X := X) hB0 hcall hfunc hslots hbody hterm hregs hty hsig (ρ₀ := ρ₀) hmr hmr'
    hargs hreg h29 hstk
  ⟨k, ρ₁, w₁, w₁', h1.star, h2, h3, h4.star, h5, h6, h7.star⟩

/-- **`entry_step2P` with the paired run guarded** (`entry_step2PDG` at `csem`). -/
theorem entry_step2PD (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR) {ctx' : FnCtx} {X : ExtSem}
    (_hs : sem = csem F ctx' X)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ w₀' : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hmr' : MR slots cs.mem w₀') (hargs : ArgsAtEntry F f.sig args w₀)
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) :
    ∃ k ρ₁ w₁ w₁', Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, k, ρ₁, w₁⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ ∧ SameWorld F w₁ w₀ ∧
      Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, k, ρ₁, w₁'⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁'⟩ ∧ SameWorld F w₁' w₀' ∧
      Star (VStep vc (pairSemD sem F ctx' X)) (.run ⟨0, 0, ρ₀, (w₀, w₀')⟩)
        (.run ⟨0, k, ρ₁, (w₁, w₁')⟩) :=
  entry_step2PDG H hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hmr' hargs
    hreg h29 hstk


end

end Backend.Proof.Driver
