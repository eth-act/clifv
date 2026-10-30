import FV.E2E.DeadCleanupExecPeak
import FV.E2E.DeadCleanupExecGoodRunT
import FV.E2E.ExecGotT
import FV.E2E.DeadCleanupExecGoodReadsT
import FV.E2E.DeadCleanupExecRunNT

/-! # Typed copies of `FV.E2E.DeadCleanupExecPeak` (S11e6, #419)

The declarations of `FV.E2E.DeadCleanupExecPeak` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okBCleanup`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`), as `FV.E2E.ExecProvenT` for the baseline
pipeline: the executable theorem at the run's peak call depth `d` (`Clif.DepthLe`), the stack
`frameDrop + D * d` (`LinkSys.budget_KT`), any program, recursive ones included.

* `DeadCleanupBinary.binary_correct_peakXT`: the model's refinement, its difference from the
  machine state, `RunGoodL` of the linked system;
* `DeadCleanupExecBytes.sysSK_entryT`, `runGood_sysSK_peakT`; `got_of_goodKT` (D4 at any budget);
* `DeadCleanupExecBytes.exec_of_runGoodT`, `binary_correct_exec_peak_provenT`.
-/

namespace E2E
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck

namespace DeadCleanupBinary

/-- **The model state differs from `r` only at the bytes `R`** (the binary factsT, the loader
premise). -/
theorem BinFactsT.modelOf_neT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) {f : Clif.Function}
    {r : Arm.ArmState} (hX : X.Intact r) : ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  intro a hne
  by_cases hi : img I a
  · rw [mem_modelOf_img hi] at hne
    rcases (hbin.code a hi).2 with h | h
    · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
    · exact h
  · exact absurd (mem_modelOf_not hi) hne

/-- **`binary_correctX` for the run's peak call depth** (the cleanup input, typed): the
whole-program CLIF run of at most `F + 1` steps reaches no state with more than `d` callers
(`Clif.DepthLe`); the stack premise is the depth-`d` budget `frameDrop + D * d`, the linked
machine has depth `d`. The run premise `TrapsExplicit` is under `Clif.linkEnvD`. -/
theorem binary_correct_peakXT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach d f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (F + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c) →
      (sys I B).RunGoodL d f (modelOf I f r)) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (I.D * d) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f (I.D * d) r)).Img a →
      worldF I f (I.D * d) r a := fun _ h => .inr h
  have hL := okBCleanup_soundT hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesT hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_peakXT _ hL (LinkSys.budget_KT _ hL)
    (Clif.Program.func?_some hf).1 F d hent hres rfl hgfree himg hbe hargs hr.entry hsav hrel hpl
    hd htr
  refine ⟨?_, hbin.modelOf_neT hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * d) r)]
  exact hA

end DeadCleanupBinary

namespace DeadCleanupExecBytes

open E2E.DeadCleanupBinary E2E.BinCheck Elf

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The entry premises of the whole-program theorems for the system keeping the slots** `S`
with the callees' stack `K` (the outside caller's stack `frameDrop + K`), for the typed
contract. -/
theorem sysSK_entryT {D : List Clif.DataObject} (hI : okBCleanupT I = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat}
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    (sysSK I B f K r S).OkT ∧
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackAvail K (art I f).af (modelOf I f r) ∧
    (∀ a, (sysSK I B f K r S).Img a →
      ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧
    StackArgsAvoid (sysSK I B f K r S).Img f.sig args (modelOf I f r) ∧
    Rel.holds ⟨(sysSK I B f K r S).F, (sysSK I B f K r S).syms, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sysSK I B f K r S).NeedSlots →
      (sysSK I B f K r S).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f K r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f K r)).Img a →
      worldF I f K r a := fun _ h => .inr h
  have hL0 := okBCleanup_soundT hI hB' himgF
  have hfacts := binFacts_of_checksT hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesT hL0 hfm hro ho hr
  have hL : (sysSK I B f K r S).OkT := LinkSys.OkT.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_factsT hL0 hfm
  have hN := ho.stack
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine ⟨hL, hent, hres, fun a ha => ?_, hbe, hargs, fun off v hm k hk hx => ?_,
    ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1, hrel.2.2.1, fun j hj => ?_,
      hrel.2.2.2.2⟩, hpl⟩
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
    show StackBelow (frameDrop (art I f).af + K) _ _
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **`RunGoodL` of the system keeping the slots for the run's peak call depth** `d`, for the
typed contract: the whole-program run of at most `F + 1` steps reaches no state with more than
`d` callers (`Clif.DepthLe`); the budget `D * d` (`LinkSys.budget_KT`), the stack
`frameDrop + D * d` (`backend_correct_program_peakXT`). -/
theorem runGood_sysSK_peakT {D : List Clif.DataObject} (hI : okBCleanupT I = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c)) :
    (sysSK I B f (I.D * d) r S).RunGoodL d f (modelOf I f r) := by
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysSK_entryT hI hbin hB hfm hX ho hav hr
  exact (backend_correct_program_peakXT (sysSK I B f (I.D * d) r S) hL
    ((LinkSys.budget_KT _ (okBCleanup_soundT hI (baseOk_F hB) fun _ h => .inr h)).extImg _ _ _) hfm
    F d hent hres rfl hgfree (fun a _ => rfl) hbe hargs hr.entry hsav hrel hpl hd htr).2 hout

/-- **D4 from the per-state facts** of the system keeping the GOT slots with any callees' budget,
for the typed contract (`got_of_goodT`, whose system fixes the stack bound of a non-recursive
program). -/
theorem got_of_goodKT {D : List Clif.DataObject} (hI : okBCleanupT I = true)
    (hbin : E2E.DeadCleanupBinCheck.BinOk I D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M Kc : Nat}
    {c t : Arm.ArmState} (hgood : (sysSK I B f Kc r (GotSlot I file)).GoodAt M g c t) :
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

/-- **The executable's run from the model-level facts** (the cleanup input, typed): for an entry
`hent` of the model state, the model's refinement `hA` of an outcome `o`, the model state
differing from `r` only at the relocated instruction bytes, and (for a returning or trapping `o`)
`RunGoodL` of the linked system and of the one keeping the GOT slots with some callees' budget
`K`, the executable machine run from `r` refines `o`. -/
theorem exec_of_runGoodT {D : List Clif.DataObject}
    (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → DeadCleanupBinCheck.RelocAt I a)
    {o : Clif.Outcome}
    (hA : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysSK I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (DeadCleanupBinCheck.RelocAt I) o := by
  by_cases hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)
  · obtain ⟨hG, hgS⟩ := hgood hout
    have hL' := okBCleanup_soundT hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkT hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine exec_of_modelNT hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside hd
      (runOkSN_of_nT hI hcm hF hH hfm (runOkN_of_goodT hI hcm hF
        (fun g hg => destsInt_of_okT hL' hg) hfm hra hG fun M' g t hR he => ?_)) hA
    obtain ⟨c', hRL, -⟩ := reachL_of_reachNT hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hg := reachN_mem hR hfm
    have hRL' : (sysSK I B f K r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg (DeadCleanupBinary.reachL_F (F' := fun _ => False) hRL)
    exact ⟨insn_of_goodT hI hcm hF hg (hG _ _ _ _ hRL he), got_of_goodKT hI hbin hgot hX hg
      (hF g hg) (hgS _ _ _ _ hRL' (by rw [mach_sysSK]; exact he))⟩
  · cases o with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, rfl⟩) hout
    | trapped c => exact absurd (.inr ⟨c, rfl⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- **The binary theorem about the executable's own words for the run's peak call depth** (the
cleanup input, typed; `E2E.ExecBytes.binary_correct_exec_peak_provenT` for the baseline): any
program, recursive ones included, the stack `frameDrop + D * d` where `d` bounds the call depth
of the whole-program CLIF run (`Clif.DepthLe`), independent of its fuel `F`. -/
theorem binary_correct_exec_peak_provenT {D : List Clif.DataObject}
    (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (DeadCleanupBinCheck.RelocAt I) (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  have hfacts := binFacts_of_checksT hI hbin
  obtain ⟨hA, hdiff, hG⟩ := binary_correct_peakXT hfacts B hB hf F d hX ho hr hd htr
  have hfm := (Clif.Program.func?_some hf).1
  have hL := okBCleanup_soundT hI (baseOk_F (F' := worldF I f (I.D * d) r) hB) fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
  exact exec_of_runGoodT hI hcm hbin hgot hB hH hfm hX hent hdiff hA fun hout =>
    ⟨hG hout, runGood_sysSK_peakT hI hbin hB hfm F d hX ho hav hr hd htr hout⟩

end DeadCleanupExecBytes

end E2E
