import FV.Link.ProductionExeWith
import FV.Link.Ld.Plan
import FV.Backend.Proof.StockScalarAddSource
import FV.Backend.Lowering.StockScalarProduction
import FV.Clif.Print

/-! Complete machine/source boundary witness for the actual production compiler.
Fixed native checks establish concrete compiler data only. The two entry arguments and their machine upper bits are
arbitrary and the executable refinement follows from the standard-only root. -/
set_option autoImplicit false
namespace E2E.ScalarAddBoundaryWitness
open Backend Backend.Proof Link E2E.LinkCheck E2E.BinCheck E2E.ProductionBinary E2E.ProductionExecBytes
open Backend.Stock.D0
variable (config : Configuration)

def name : String := "production_boundary"
def text (config : Configuration) : String := (Stock.ScalarAdd.source name config []).print
def initial (config : Configuration) : LinkSpec := {
  funcs := [{clif := text config,ra := "null"}]
  names := []
  sizes := []
  outside := []
  symNames := [name]
  R := 0x200160 }
def spec (config : Configuration) (cleanup : Bool) : LinkSpec := (initial config).placedProductionWith Stock.ScalarAdd.lower cleanup

def plan (S : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + S.size
  {base := 0x200000,entry := S.R,
   segs := [{kind := 1,vaddr := 0x200000,offset := 0,filesz := size,memsz := size}],
   tlsAddr := 0x200000+size,tlsOff := size,tlsFilesz := 0,tlsMemsz := 0,tlsAlign := 1,
   ehOff := 0,ehAddr := 0,ehSize := 0,size,pieces := [],secs := #[],
   syms := S.addrs.toArray.map fun (n,v) => {name := symName n,value := v,info := 18,shndx := 0xfff1}}
def file0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (plan (spec config cleanup)) with | .ok im => im.write | .error _ => ByteArray.empty
def file (config : Configuration) (cleanup : Bool) : ByteArray :=
  getOk (Link.ProductionCompilerWith.attempt Stock.ScalarAdd.lower (spec config cleanup) (file0 config cleanup) cleanup)
def input (config : Configuration) (cleanup : Bool) : ProductionStackBound.CompilerInput := Link.ProductionCompilerWith.input Stock.ScalarAdd.lower (spec config cleanup) cleanup
def f (config : Configuration) : Clif.Function := Stock.ScalarAdd.source name config []
def argument (config : Configuration) (word : BitVec (valueType config).width) : Clif.Val := ⟨valueType config,word⟩
def cm (config : Configuration) (cleanup : Bool) : Clif.Mem := {Clif.Mem.empty with symbols := fun n => (input config cleanup).syms.lookup n}
def entered (config : Configuration) (cleanup : Bool) : Clif.Mem := (Clif.enterSlots (f config) (cm config cleanup)).2
def cs (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) : Clif.State :=
  ⟨Stock.ScalarAdd.Source.frame name config [] u v,[],entered config cleanup⟩
def machineWord (config : Configuration) (word : BitVec (valueType config).width) (upper : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (upper * 2^(valueType config).width + word.toNat)
def machine (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width)
    (upper0 upper1 : Nat) : Arm.ArmState :=
  Arm.w .PC (art (input config cleanup) (f config)).base
    (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 30#5) 0x8000000#64
        (Arm.w (.GPR 1#5) (machineWord config v upper1)
          (Arm.w (.GPR 0#5) (machineWord config u upper0)
            {Arm.ArmState.default with mem := fun a => (Elf.loadMem (file config cleanup) a).getD 0}))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem compiler_success (config : Configuration) (cleanup : Bool) :
    Link.ProductionCompilerWith.attempt Stock.ScalarAdd.lower (spec config cleanup) (file0 config cleanup) cleanup = .ok (file config cleanup) := by
  cases config <;> cases cleanup <;> native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem concrete_facts (config : Configuration) (cleanup : Bool) :
    (prog (input config cleanup)).funcs = [(f config)] ∧
    ProductionStackBound.stackFn (input config cleanup) (f config) ≤ 4096 ∧
    ProductionStackBound.goodN (input config cleanup) name = true ∧
    (tabOf (input config cleanup).results).all
      (fun e => decide (e.2.base.toNat + 4*e.2.fb.words.size ≤ 0x210000)) = true := by
  cases config <;> cases cleanup <;> native_decide

theorem image_bound {I : ProductionStackBound.CompilerInput} {limit : Nat}
    (hl : limit ≤ 2^64)
    (hb : (tabOf I.results).all (fun e => decide (e.2.base.toNat + 4*e.2.fb.words.size ≤ limit)) = true)
    {a : BitVec 64} (ha : img I a) : a.toNat < limit := by
  obtain ⟨e,he,p,hp,hlt⟩ := ha
  obtain ⟨j,hj,hp1⟩ := mem_wordsAt (k := 0) hp
  simp only [Nat.zero_add] at hp1
  have hjl : j < e.2.fb.words.size := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa using this
  have bounds := of_decide_eq_true (List.all_eq_true.mp hb e he)
  have eq : a = wAt e.2 (4*j+(a-p.1).toNat) := by
    simp only [wAt]
    rw [BitVec.ofNat_add,← BitVec.add_assoc,← hp1,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      BitVec.add_comm,BitVec.sub_add_cancel]
  have ho : 4*j+(a-p.1).toNat < 2^64 := by omega
  have hs : e.2.base.toNat + (4*j+(a-p.1).toNat) < 2^64 := by omega
  rw [eq,wAt,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ho,Nat.mod_eq_of_lt hs]
  omega

theorem machine_x0 (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) : xreg 0 (machine config cleanup u v upper0 upper1) = machineWord config u upper0 := by
  simp [xreg,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem machine_x1 (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width)
    (upper0 upper1 : Nat) : xreg 1 (machine config cleanup u v upper0 upper1) = machineWord config v upper1 := by
  simp [xreg,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem machine_ra (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) : xreg 30 (machine config cleanup u v upper0 upper1) = 0x8000000#64 := by
  simp [xreg,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem machine_sp (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) : spv (machine config cleanup u v upper0 upper1) = 0x1000000#64 := by
  simp [spv,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem locations (config : Configuration) : locsOf (f config).sig = [.reg (.x 0),.reg (.x 1)] := by cases config <;> rfl

theorem outside_call (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) :
    OutsideCall (input config cleanup) (roByte (input config cleanup) (spec config cleanup).data) (f config)
      (ProductionStackBound.stackFn (input config cleanup) (f config)) (machine config cleanup u v upper0 upper1)
      [argument config u,argument config v] (entered config cleanup) where
  pc := by simp [machine,Arm.r_of_w_same]
  err := by
    unfold machine
    rw [Arm.r_of_w_different (by decide),Arm.r_of_w_different (by decide),
      Arm.r_of_w_different (by decide),Arm.r_of_w_different (by decide),Arm.r_of_w_different (by decide)]
    simp [Arm.r,Arm.read_base_error,Arm.ArmState.default]
  ra := by
    intro h
    have hb := image_bound (by decide) (concrete_facts config cleanup).2.2.2 h
    rw [machine_ra config] at hb
    change 0x8000000 < 0x210000 at hb
    omega
  spAligned := by rw [machine_sp config]; decide
  stack := by
    rw [machine_sp config]
    change ProductionStackBound.stackFn (input config cleanup) (f config) ≤ 0x1000000
    have := (concrete_facts config cleanup).2.1
    omega
  stackFree := by
    intro a ha hs
    have hb := image_bound (by decide) (concrete_facts config cleanup).2.2.2 ha
    have hn := (concrete_facts config cleanup).2.1
    rw [machine_sp config] at hs
    change a.toNat < 0x1000000 ∧ 0x1000000 ≤ a.toNat + ProductionStackBound.stackFn (input config cleanup) (f config) at hs
    omega
  args := by
    intro loc val h
    simp only [locations,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,
      List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [argument,regVal,VHolds]
      change (xreg 0 (machine config cleanup u v upper0 upper1)).setWidth (valueType config).width = u
      rw [machine_x0]
      exact Stock.ScalarAdd.Source.dirty_machine_bits config u upper0
    · simp [argument,regVal,VHolds]
      change (xreg 1 (machine config cleanup u v upper0 upper1)).setWidth (valueType config).width = v
      rw [machine_x1]
      exact Stock.ScalarAdd.Source.dirty_machine_bits config v upper1

  bytes := by intro a b hv; simp [entered,f,Stock.ScalarAdd.source,Stock.D0.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  image := by intro a b b' hv; simp [entered,f,Stock.ScalarAdd.source,Stock.D0.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  valid := by intro a n hv; simp [entered,f,Stock.ScalarAdd.source,Stock.D0.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  symbols := rfl

theorem intact (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) :
    (imageOf (file config cleanup)).Intact (machine config cleanup u v upper0 upper1) := by
  intro a b _ hb
  simp only [machine,Arm.ArmState.mem_w_eq_mem]
  change (Elf.loadMem (file config cleanup) a).getD 0 = b
  change Elf.loadMem (file config cleanup) a = some b at hb
  rw [hb]
  rfl

theorem program_find (config : Configuration) (cleanup : Bool) : (prog (input config cleanup)).func? name = some (f config) := by
  unfold Clif.Program.func?
  rw [(concrete_facts config cleanup).1]
  rfl

theorem source_entry (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) :
    ClifEntry (f config) [argument config u,argument config v] (cs config cleanup u v) := by
  apply clifEntry_initState (mem := cm config cleanup) (program_find config cleanup)
  have hf : (prog (input config cleanup)).func? (f config).name = some (f config) := program_find config cleanup
  simp only [Clif.initState,hf,Clif.Res.ofOption_some,Clif.Res.ok_bind]
  have h := Stock.ScalarAdd.Source.source_entry name config [] u v (cm config cleanup)
  change Clif.enterFunc (f config) [argument config u,argument config v] (cm config cleanup) =
    .ok (Stock.ScalarAdd.Source.frame name config [] u v,entered config cleanup) at h
  rw [h]
  rfl

theorem clif_run (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) :
    ClifRun (input config cleanup) closedBase (f config) (machine config cleanup u v upper0 upper1) [argument config u,argument config v] (cs config cleanup u v) where
  entry := source_entry config cleanup u v
  slots := by simp [SlotRel,f,cs,Stock.ScalarAdd.Source.frame,Stock.ScalarAdd.source,Stock.D0.source,slotLayout]
  place := by
    rintro ⟨g,hg,h,hc,hslots⟩
    have hh := LinkSys.callee_mem (sys (input config cleanup) closedBase) hc
    change h ∈ (prog (input config cleanup)).funcs at hh
    rw [(concrete_facts config cleanup).1] at hh
    simp only [List.mem_singleton] at hh
    subst h
    exact (hslots rfl).elim

theorem base_ok (config : Configuration) (cleanup : Bool) : BaseOk (sys (input config cleanup) closedBase) := by
  apply baseOk_closedR
  intro g hg
  change g ∈ (prog (input config cleanup)).funcs at hg
  rw [(concrete_facts config cleanup).1] at hg
  simp only [List.mem_singleton] at hg
  subst g
  cases config <;> decide +kernel

theorem source_returns (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) :
    Clif.runLoop closedBase.env (prog (input config cleanup)) 2 (cs config cleanup u v) =
      .returned [argument config (u+v)] (cm config cleanup) := by
  have h := Stock.ScalarAdd.Source.source_return name config [] u v (entered config cleanup)
    closedBase.env (prog (input config cleanup))
  change Clif.runLoop closedBase.env (prog (input config cleanup)) 2 (cs config cleanup u v) =
    .returned [argument config (u+v)] (((Clif.enterSlots (f config) (cm config cleanup)).2).free []).leave at h
  have hm := Stock.ScalarAdd.Source.source_memory_roundtrip name config [] (cm config cleanup)
  change (((Clif.enterSlots (f config) (cm config cleanup)).2).free []).leave = cm config cleanup at hm
  rw [hm] at h
  exact h

theorem executable_witness (config : Configuration) (cleanup : Bool) (u v : BitVec (valueType config).width) (upper0 upper1 : Nat) :
    ExecRefines (art (input config cleanup) (f config)).fb (art (input config cleanup) (f config)).base
      (xreg 30 (machine config cleanup u v upper0 upper1)) (step (input config cleanup) closedBase (file config cleanup))
      (machine config cleanup u v upper0 upper1) (RelocAtWithResults (input config cleanup) (input config cleanup).results)
      (.returned [argument config (u+v)] (cm config cleanup)) := by
  have hI := (Link.ProductionCompilerWith.attempt_spec (compiler_success config cleanup)).1
  have hf := program_find config cleanup
  have hfm := (Clif.Program.func?_some hf).1
  have hL : (ProductionStackBound.ofInput (input config cleanup) closedBase (img (input config cleanup))).OkProduction :=
    ProductionStackBound.okB_sound hI (baseOk_F (base_ok config cleanup)) (fun _ h => h)
  obtain ⟨g,hg,hcyc⟩ := (ProductionStackBound.goodN_iff hI).mp (concrete_facts config cleanup).2.2.1
  have hg' : g = (f config) := Option.some.inj (hg.symm.trans hf)
  subst g
  have htr := trapsExplicit_of_run hL hfm (source_entry config cleanup u v)
    (outside_call config cleanup u v upper0 upper1).symbols (source_returns config cleanup u v)
  have proof := Link.ProductionCompilerWith.attempt_correct (compiler_success config cleanup) closedBase
    (base_ok config cleanup) (hooksSim_closed _) hf hcyc 1
    (r := machine config cleanup u v upper0 upper1) (args := [argument config u,argument config v]) (cs := cs config cleanup u v) (intact config cleanup u v upper0 upper1)
    (outside_call config cleanup u v upper0 upper1) (clif_run config cleanup u v upper0 upper1) htr
  have result : ExecRefines (art (input config cleanup) (f config)).fb (art (input config cleanup) (f config)).base
      (xreg 30 (machine config cleanup u v upper0 upper1)) (step (input config cleanup) closedBase (file config cleanup))
      (machine config cleanup u v upper0 upper1) (RelocAtWithResults (input config cleanup) (input config cleanup).results)
      (Clif.runLoop closedBase.env (prog (input config cleanup)) 2 (cs config cleanup u v)) := proof
  rw [source_returns config] at result
  exact result

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem actual_stock_history (config : Configuration) (cleanup : Bool) :
    (art (input config cleanup) (f config)).vc.rulesFired ≠ (getOk (lowerFunction (f config))).rulesFired := by
  cases config <;> cases cleanup <;> native_decide

end E2E.ScalarAddBoundaryWitness
