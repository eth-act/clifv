import FV.E2E.DeadCleanupExecGot
import FV.E2E.DeadCleanupExecGoodRunT
import FV.E2E.ExecGotT
import FV.E2E.DeadCleanupBinaryT
import FV.E2E.DeadCleanupBinCheckT
import FV.E2E.BinCheckT
import FV.E2E.BinaryGoodT
import FV.E2E.BinaryT
import FV.E2E.DeadCleanupBinaryGoodT
import FV.E2E.DeadCleanupExecBytesT
import FV.E2E.DeadCleanupExecRunNT
import FV.E2E.DeadCleanupExecStaticT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.DeadCleanupStackBoundT
import FV.E2E.ExecBytesT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkGoodT
import FV.E2E.PipelineCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.DeadCleanupExecGot` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecGot` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck Elf
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **`RunGoodL` of the system keeping the slots**, for a returning or trapping outcome. -/
theorem runGood_sysST {D : List Clif.DataObject} (hI : okBCleanupT I = true) (hbin : E2E.DeadCleanupBinCheck.BinOk I D file)
    (hB : BaseOk (sys I B)) {n : String} (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f r S).RunGoodL M f (modelOf I f r) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).Img a →
      worldF I f (DeadCleanupStackBound.bud I f) r a := fun _ h => .inr h
  have hL0 := okBCleanup_soundT hI hB' himgF
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checksT hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesT hL0 hfm hro ho hr
  have hL : (sysS I B f r S).OkT := LinkSys.OkT.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  have hn' := hn
  unfold DeadCleanupStackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsT hL0 hfm
  have hN := ho.stack
  have hN' : frameDrop (art I f).af + DeadCleanupStackBound.bud I f ≤ (spv r).toNat := hN
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine (backend_correct_program_stackXT (sysS I B f r S) hL
    ((DeadCleanupStackBound.budget_ofT hI B (worldF I f (DeadCleanupStackBound.bud I f) r)).extImg _ _ _)
    (DeadCleanupStackBound.bud I f) (fun M => by simp [LinkSys.hybrid, hb, hbud]) hfm M hent
    (by rw [spv_modelOf]; exact hN) (fun a ha => ?_) rfl (fun a _ => rfl) hbe hargs hr.entry
    (fun off v hm k hk hx => ?_) ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1,
      hrel.2.2.1, fun j hj => ?_, hrel.2.2.2.2⟩ hpl htr).2 hout
  · rcases ha with ha | ha
    · exact hgfree a ha
    · rw [spv_modelOf]; exact hav.stack a ha
  · rcases hx with hx | hx
    · exact hsav off v hm k hk hx
    · rw [spv_modelOf] at hx; exact hav.args off v hm k hk hx
  · obtain ⟨hfit, hk⟩ := hrel.1.valid a n hv
    exact ⟨hfit, fun k hkn => not_worldFS (hk k hkn) (hav.valid a n hv k hkn)⟩
  · refine not_worldFS (hrel.2.2.2.1 j hj) fun hS => hav.stack _ hS ?_
    change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
    rw [hspb]
    show StackBelow (frameDrop (art I f).af + DeadCleanupStackBound.bud I f) _ _
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **D4 from the per-state facts** of the system keeping the GOT slots: at the `ldr` of a GOT
pair, the slot's bytes are the activation's entry bytes (`RL.GoodX.got`, the slots kept), which
are the model state's, which are the file's (`GotOk`, `img_bytesT`, `Image.Intact`). -/
theorem got_of_goodT {D : List Clif.DataObject} (hI : okBCleanupT I = true) (hbin : E2E.DeadCleanupBinCheck.BinOk I D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M : Nat}
    {c t : Arm.ArmState} (hgood : (sysS I B f r (GotSlot I file)).GoodAt M g c t) :
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ E2E.DeadCleanupBinCheck.RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0 := by
  intro rl hrl ht hpc rd G hrd h8 hin hw0 hw1 i hi
  obtain ⟨X, K, G', gv, -, hG, himgG, himgS, -⟩ := hgood
  unfold actGoodX at hG
  have hS : GotSlot I file (BitVec.ofNat 64 G + BitVec.ofNat 64 i) :=
    ⟨_, tab_mem (okBCleanup_namesT hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
  obtain ⟨hkept, hsome, hnr⟩ := hgot _ hS
  refine ⟨hnr, ?_⟩
  -- the `ldr` line
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hFg hrl (.inl ht)
  obtain ⟨j2, i2, t2, hj2, hi2, ho2⟩ := (FnAsm.layout_relocs hFg.layout r').1 hr'
  obtain ⟨a1, b1, c1, rfl⟩ : ∃ a b c, i2 = .ldrGotLo12 a b c := by
    rw [hr't, ht] at hi2
    cases i2 <;> simp [Insn.reloc?, loOf] at hi2
    exact ⟨_, _, _, rfl⟩
  have hat := hG.got a1 b1 c1 ⟨j2, t2, hj2, by
    rw [hpc, ← hr'o, ← ho2]; rfl⟩ _ (himgG _ (.inr hS))
  rw [hat, himgS _ (.inr hS)]
  show (modelOf I f r).mem _ = _
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  rw [hb, Option.getD_some]
  by_cases hii : img I (BitVec.ofNat 64 G + BitVec.ofNat 64 i)
  · rw [mem_modelOf_img hii]
    rcases (DeadCleanupBinCheck.img_bytesT hbin hI hii).2 with h | h
    · rw [hb] at h; cases h; rfl
    · exact absurd h hnr
  · rw [mem_modelOf_not hii]
    exact hX _ _ hkept hb

/-- **`binary_correct_exec_of_reads` with D4 discharged**: under the premises of
`binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the code map check
`codeMapB`, the GOT check's fact `GotOk` (`gotB_sound`), the outside caller keeping the GOT slots
off its stack and CLIF memory (`OutsideAvoids`), and only the memory-read fact D2 (`RunInsnN`)
of the model's run, the executable machine run from `r` refines the whole-program CLIF run. -/
theorem binary_correct_exec_of_insnT {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hins : RunInsnN I B file M f (modelOf I f r)) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iffT hI).2 ⟨f, hf, hc⟩
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · obtain ⟨-, -, hG⟩ := binary_correct_of_checksXT hI hbin B hB hn hf M hX ho hr htr
    have hgS := runGood_sysST hI hbin hB hn hf M hX ho hav hr htr hout
    have hfm := (Clif.Program.func?_some hf).1
    have hL' := okBCleanup_soundT hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkT hI hbin hL' hg
    have hent : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      have hB'' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
      have hL0 := okBCleanup_soundT hI hB'' fun _ h => .inr h
      have hfacts := binFacts_of_checksT hI hbin
      have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
        hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
      obtain ⟨he, -⟩ := premisesT hL0 hfm hro ho hr
      simp only [xreg, r_modelOf]; exact he.raOutside
    refine binary_correct_exec_of_readsT hI hcm hbin B hB hH hf hc M hX ho hr htr
      fun M' g t hR he => ⟨hins M' g t hR he, ?_⟩
    obtain ⟨c', hRL, -⟩ := reachL_of_reachNT hI hcm hF hR hfm (hG hout)
      (raNotSecond_top (hF f hfm) hent)
    have hRL' : (sysS I B f r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t := by
      exact LinkSys.reachL_extImg (F := worldFS I f (DeadCleanupStackBound.bud I f) r (GotSlot I file))
        (S := GotSlot I file) (m := (modelOf I f r).mem)
        (E2E.DeadCleanupBinary.reachL_F (F := worldF I f (DeadCleanupStackBound.bud I f) r) (F' := fun _ => False) hRL)
    have hg := reachN_mem hR hfm
    exact got_of_goodT hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial
end E2E.DeadCleanupExecBytes
