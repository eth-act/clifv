import FV.Opt.Proof.LegalArith
import FV.Link.ProductionExe
import FV.Link.Ld.Plan
import FV.Backend.Proof.StockPrologueSource

/-! Complete machine/source boundary witness for the actual production compiler.
Fixed native checks establish concrete compiler data only. The entry argument is
arbitrary and the executable refinement follows from the standard-only root. -/
set_option autoImplicit false
namespace E2E.ProductionBoundaryWitness
open Backend Backend.Proof Link E2E.LinkCheck E2E.BinCheck E2E.ProductionBinary E2E.ProductionExecBytes

def name : String := "production_boundary"
def text : String :=
  "function %production_boundary(i64) -> i64 system_v {\nblock0(v0: i64):\n    nop\n    jump block1\nblock1:\n    nop\n    return v0\n}\n"
def initial : LinkSpec := {
  funcs := [{clif := text,ra := "null"}]
  names := []
  sizes := []
  outside := []
  symNames := [name]
  R := 0x200160 }
def spec (cleanup : Bool) : LinkSpec := initial.placedProduction cleanup

def plan (S : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + S.size
  {base := 0x200000,entry := S.R,
   segs := [{kind := 1,vaddr := 0x200000,offset := 0,filesz := size,memsz := size}],
   tlsAddr := 0x200000+size,tlsOff := size,tlsFilesz := 0,tlsMemsz := 0,tlsAlign := 1,
   ehOff := 0,ehAddr := 0,ehSize := 0,size,pieces := [],secs := #[],
   syms := S.addrs.toArray.map fun (n,v) => {name := symName n,value := v,info := 18,shndx := 0xfff1}}
def file0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (plan (spec cleanup)) with | .ok im => im.write | .error _ => ByteArray.empty
def file (cleanup : Bool) : ByteArray :=
  getOk (Link.ProductionCompiler.attempt (spec cleanup) (file0 cleanup) cleanup)
def input (cleanup : Bool) : ProductionStackBound.CompilerInput := Link.ProductionCompiler.input (spec cleanup) cleanup
def f : Clif.Function := Clif.StockPrologueSource.source name []
def argument (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
def cm (cleanup : Bool) : Clif.Mem := {Clif.Mem.empty with symbols := fun n => (input cleanup).syms.lookup n}
def entered (cleanup : Bool) : Clif.Mem := (Clif.enterSlots f (cm cleanup)).2
def cs (cleanup : Bool) (word : BitVec 64) : Clif.State :=
  ⟨Clif.StockPrologueSource.frame name [] word,[],entered cleanup⟩
def machine (cleanup : Bool) (word : BitVec 64) : Arm.ArmState :=
  Arm.w .PC (art (input cleanup) f).base
    (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 30#5) 0x8000000#64 (Arm.w (.GPR 0#5) word
        {Arm.ArmState.default with mem := fun a => (Elf.loadMem (file cleanup) a).getD 0})))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem compiler_success (cleanup : Bool) :
    Link.ProductionCompiler.attempt (spec cleanup) (file0 cleanup) cleanup = .ok (file cleanup) := by
  cases cleanup <;> native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem concrete_facts (cleanup : Bool) :
    (prog (input cleanup)).funcs = [f] ∧
    ProductionStackBound.stackFn (input cleanup) f ≤ 4096 ∧
    ProductionStackBound.goodN (input cleanup) name = true ∧
    (tabOf (input cleanup).results).all
      (fun e => decide (e.2.base.toNat + 4*e.2.fb.words.size ≤ 0x210000)) = true := by
  cases cleanup <;> native_decide

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

theorem machine_x0 (cleanup : Bool) (word : BitVec 64) : xreg 0 (machine cleanup word) = word := by
  simp [xreg,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem machine_ra (cleanup : Bool) (word : BitVec 64) : xreg 30 (machine cleanup word) = 0x8000000#64 := by
  simp [xreg,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem machine_sp (cleanup : Bool) (word : BitVec 64) : spv (machine cleanup word) = 0x1000000#64 := by
  simp [spv,machine,Arm.r_of_w_same,Arm.r_of_w_different]
theorem locations : locsOf f.sig = [.reg (.x 0)] := by rfl

theorem outside_call (cleanup : Bool) (word : BitVec 64) :
    OutsideCall (input cleanup) (roByte (input cleanup) (spec cleanup).data) f
      (ProductionStackBound.stackFn (input cleanup) f) (machine cleanup word)
      [argument word] (entered cleanup) where
  pc := by simp [machine,Arm.r_of_w_same]
  err := by
    unfold machine
    rw [Arm.r_of_w_different (by decide),Arm.r_of_w_different (by decide),
      Arm.r_of_w_different (by decide),Arm.r_of_w_different (by decide)]
    simp [Arm.r,Arm.read_base_error,Arm.ArmState.default]
  ra := by
    intro h
    have hb := image_bound (by decide) (concrete_facts cleanup).2.2.2 h
    rw [machine_ra] at hb
    change 0x8000000 < 0x210000 at hb
    omega
  spAligned := by rw [machine_sp]; decide
  stack := by
    rw [machine_sp]
    change ProductionStackBound.stackFn (input cleanup) f ≤ 0x1000000
    have := (concrete_facts cleanup).2.1
    omega
  stackFree := by
    intro a ha hs
    have hb := image_bound (by decide) (concrete_facts cleanup).2.2.2 ha
    have hn := (concrete_facts cleanup).2.1
    rw [machine_sp] at hs
    change a.toNat < 0x1000000 ∧ 0x1000000 ≤ a.toNat + ProductionStackBound.stackFn (input cleanup) f at hs
    omega
  args := by
    simp [ArgsOut,locations,argument,regVal,VHolds]
    simpa [xreg,rnum] using machine_x0 cleanup word
  bytes := by intro a b hv; simp [entered,f,Clif.StockPrologueSource.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  image := by intro a b b' hv; simp [entered,f,Clif.StockPrologueSource.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  valid := by intro a n hv; simp [entered,f,Clif.StockPrologueSource.source,Clif.enterSlots,Clif.bumpSlots,cm,Clif.Mem.valid,Clif.Mem.empty] at hv
  symbols := rfl

theorem intact (cleanup : Bool) (word : BitVec 64) :
    (imageOf (file cleanup)).Intact (machine cleanup word) := by
  intro a b _ hb
  simp only [machine,Arm.ArmState.mem_w_eq_mem]
  change (Elf.loadMem (file cleanup) a).getD 0 = b
  change Elf.loadMem (file cleanup) a = some b at hb
  rw [hb]
  rfl

theorem program_find (cleanup : Bool) : (prog (input cleanup)).func? name = some f := by
  unfold Clif.Program.func?
  rw [(concrete_facts cleanup).1]
  rfl

theorem source_entry (cleanup : Bool) (word : BitVec 64) :
    ClifEntry f [argument word] (cs cleanup word) := by
  apply clifEntry_initState (mem := cm cleanup) (program_find cleanup)
  have hf : (prog (input cleanup)).func? f.name = some f := program_find cleanup
  simp only [Clif.initState,hf,Clif.Res.ofOption_some,Clif.Res.ok_bind]
  have h := Clif.StockPrologueSource.source_entry name [] word (cm cleanup)
  change Clif.enterFunc f [argument word] (cm cleanup) =
    .ok (Clif.StockPrologueSource.frame name [] word,entered cleanup) at h
  rw [h]
  rfl

theorem clif_run (cleanup : Bool) (word : BitVec 64) :
    ClifRun (input cleanup) closedBase f (machine cleanup word) [argument word] (cs cleanup word) where
  entry := source_entry cleanup word
  slots := by simp [SlotRel,f,cs,Clif.StockPrologueSource.frame,Clif.StockPrologueSource.source,slotLayout]
  place := by
    rintro ⟨g,hg,h,hc,hslots⟩
    have hh := LinkSys.callee_mem (sys (input cleanup) closedBase) hc
    change h ∈ (prog (input cleanup)).funcs at hh
    rw [(concrete_facts cleanup).1] at hh
    simp only [List.mem_singleton] at hh
    subst h
    exact (hslots rfl).elim

theorem base_ok (cleanup : Bool) : BaseOk (sys (input cleanup) closedBase) := by
  apply baseOk_closedR
  intro g hg
  change g ∈ (prog (input cleanup)).funcs at hg
  rw [(concrete_facts cleanup).1] at hg
  simp only [List.mem_singleton] at hg
  subst g
  decide +kernel

theorem source_returns (cleanup : Bool) (word : BitVec 64) :
    Clif.runLoop closedBase.env (prog (input cleanup)) 4 (cs cleanup word) =
      .returned [argument word] (cm cleanup) := by
  have h := Clif.StockPrologueSource.source_body name [] word (entered cleanup)
    closedBase.env (prog (input cleanup))
  change Clif.runLoop closedBase.env (prog (input cleanup)) 4 (cs cleanup word) =
    .returned [argument word] (((Clif.enterSlots f (cm cleanup)).2).free []).leave at h
  have hm := Clif.StockPrologueSource.source_memory_roundtrip name [] (cm cleanup)
  change (((Clif.enterSlots f (cm cleanup)).2).free []).leave = cm cleanup at hm
  rw [hm] at h
  exact h

theorem executable_witness (cleanup : Bool) (word : BitVec 64) :
    ExecRefines (art (input cleanup) f).fb (art (input cleanup) f).base
      (xreg 30 (machine cleanup word)) (step (input cleanup) closedBase (file cleanup))
      (machine cleanup word) (RelocAtWithResults (input cleanup) (input cleanup).results)
      (.returned [argument word] (cm cleanup)) := by
  have hI := (Link.ProductionCompiler.attempt_spec (compiler_success cleanup)).1
  have hf := program_find cleanup
  have hfm := (Clif.Program.func?_some hf).1
  have hL : (ProductionStackBound.ofInput (input cleanup) closedBase (img (input cleanup))).OkProduction :=
    ProductionStackBound.okB_sound hI (baseOk_F (base_ok cleanup)) (fun _ h => h)
  obtain ⟨g,hg,hcyc⟩ := (ProductionStackBound.goodN_iff hI).mp (concrete_facts cleanup).2.2.1
  have hg' : g = f := Option.some.inj (hg.symm.trans hf)
  subst g
  have htr := trapsExplicit_of_run hL hfm (source_entry cleanup word)
    (outside_call cleanup word).symbols (source_returns cleanup word)
  have proof := Link.ProductionCompiler.attempt_correct (compiler_success cleanup) closedBase
    (base_ok cleanup) (hooksSim_closed _) hf hcyc 3
    (r := machine cleanup word) (args := [argument word]) (cs := cs cleanup word) (intact cleanup word)
    (outside_call cleanup word) (clif_run cleanup word) htr
  have result : ExecRefines (art (input cleanup) f).fb (art (input cleanup) f).base
      (xreg 30 (machine cleanup word)) (step (input cleanup) closedBase (file cleanup))
      (machine cleanup word) (RelocAtWithResults (input cleanup) (input cleanup).results)
      (Clif.runLoop closedBase.env (prog (input cleanup)) 4 (cs cleanup word)) := proof
  rw [source_returns] at result
  exact result

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem actual_stock_history (cleanup : Bool) :
    (art (input cleanup) f).vc.rulesFired ≠ (getOk (lowerFunction f)).rulesFired := by
  cases cleanup <;> native_decide

end E2E.ProductionBoundaryWitness
