import FV.E2E.ExecGot
import FV.E2E.BinCheckT
import FV.E2E.BinaryT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkGoodT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.ExecGot` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecGot` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E
open Backend Backend.Proof E2E.LinkCheck E2E.BinCheck Elf
namespace LinkSys

/-- **The extended system is a linked program**: the code image's facts hold for any extension
holding the image's bytes on the image, inside the exterior. -/
theorem OkT.extImg {L : LinkSys} (hL : L.OkT) {F S : BitVec 64 → Prop} {m : Arm.Memory}
    (hm : ∀ a, L.Img a → m a = L.imgMem a) (hF : ∀ a, L.Img a ∨ S a → F a) :
    (L.extImg F S m).OkT :=
  { hL with
    imgAddr := fun g hg a ha => .inl (hL.imgAddr g hg a ha)
    imgCode := fun g hg t ht => hL.imgCode g hg t fun a ha => (ht a (.inl ha)).trans (hm a ha)
    imgF := hF }
end LinkSys
namespace ExecBytes
open Binary
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The entry premises of the whole-program theorems for the system keeping the slots** `S`
with the callees' stack `K` (the outside caller's stack `frameDrop + K`): what
`backend_correct_program_budgetXT` and `backend_correct_program_peakXT` take besides the budget and
the run premisesT. -/
theorem sysS_entryT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat}
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    (sysS I B f K r S).OkT ∧
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackAvail K (art I f).af (modelOf I f r) ∧
    (∀ a, (sysS I B f K r S).Img a →
      ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧
    StackArgsAvoid (sysS I B f K r S).Img f.sig args (modelOf I f r) ∧
    Rel.holds ⟨(sysS I B f K r S).F, (sysS I B f K r S).syms, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sysS I B f K r S).NeedSlots →
      (sysS I B f K r S).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f K r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f K r)).Img a →
      worldF I f K r a := fun _ h => .inr h
  have hL0 := okB_soundT hI hB' himgF
  have hfacts := binFacts_of_checksT hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesT hL0 hfm hro ho hr
  have hL : (sysS I B f K r S).OkT := LinkSys.OkT.extImg hL0
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

/-- **`RunGoodL` of the system keeping the slots** for any callees' budget `κ` of the linked
system (`LinkSys.Budget`) whose value at the entry is `K` (the stack `frameDrop + K`), for a
returning or trapping outcome. -/
theorem runGood_sysS_ofT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat} {κ : Nat → Clif.Function → Nat}
    (hκ : (LinkSys.ofInput I B (worldF I f K r)).Budget κ) (hK : κ M f = K)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f K r S).RunGoodL M f (modelOf I f r) := by
  subst hK
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysS_entryT hI hbin hB hfm hX ho hav hr
  exact (backend_correct_program_budgetXT (sysS I B f (κ M f) r S) hL (hκ.extImg _ _ _) hfm M
    hent hres rfl hgfree (fun a _ => rfl) hbe hargs hr.entry hsav hrel hpl htr).2 hout

/-- **`RunGoodL` of the system keeping the slots**, for a returning or trapping outcome: the
stack bound of a non-recursive program (`goodN`; the budget `StackBound.budget_ofT`). -/
theorem runGood_sysST {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (StackBound.bud I f) r S).RunGoodL M f (modelOf I f r) := by
  have hf' : (progOf I.results).func? n = some f := hf
  have hn' := hn
  unfold StackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : StackBound.bud I f = b := by simp [StackBound.bud, hb]
  exact runGood_sysS_ofT hI hbin hB (Clif.Program.func?_some hf).1 M hX
    (StackBound.budget_ofT hI B (worldF I f (StackBound.bud I f) r))
    (by simp [LinkSys.hybrid, hb, hbud]) ho hav hr htr hout

/-- **`RunGoodL` of the system keeping the slots for any program**, recursive ones included: the
depth-`M` budget `D * M` (`LinkSys.budget_KT`), the stack `frameDrop + D * M`. -/
theorem runGood_sysS_depthT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (I.D * M) r S).RunGoodL M f (modelOf I f r) :=
  runGood_sysS_ofT hI hbin hB hfm M hX
    (LinkSys.budget_KT _ (okB_soundT hI (baseOk_F hB) fun _ h => .inr h)) rfl ho hav hr htr hout

/-- **`RunGoodL` of the system keeping the slots for the run's peak call depth** `d` (L1d): the
whole-program run of at most `F + 1` steps reaches no state with more than `d` callers
(`Clif.DepthLe`); the budget `D * d` (`LinkSys.budget_KT`), the stack `frameDrop + D * d`
(`backend_correct_program_peakXT`). -/
theorem runGood_sysS_peakT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c)) :
    (sysS I B f (I.D * d) r S).RunGoodL d f (modelOf I f r) := by
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysS_entryT hI hbin hB hfm hX ho hav hr
  exact (backend_correct_program_peakXT (sysS I B f (I.D * d) r S) hL
    ((LinkSys.budget_KT _ (okB_soundT hI (baseOk_F hB) fun _ h => .inr h)).extImg _ _ _) hfm F d
    hent hres rfl hgfree (fun a _ => rfl) hbe hargs hr.entry hsav hrel hpl hd htr).2 hout

/-- **D4 from the per-state facts** of the system keeping the GOT slots: at the `ldr` of a GOT
pair, the slot's bytes are the activation's entry bytes (`RL.GoodX.got`, the slots kept), which
are the model state's, which are the file's (`GotOk`, `img_bytesT`, `Image.Intact`). -/
theorem got_of_goodT {D : List Clif.DataObject} (hI : okBT I = true) (hbin : BinOk I D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M Kc : Nat}
    {c t : Arm.ArmState} (hgood : (sysS I B f Kc r (GotSlot I file)).GoodAt M g c t) :
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0 := by
  intro rl hrl ht hpc rd G hrd h8 hin hw0 hw1 i hi
  obtain ⟨X, K, G', gv, -, hG, himgG, himgS, -⟩ := hgood
  unfold actGoodX at hG
  have hS : GotSlot I file (BitVec.ofNat 64 G + BitVec.ofNat 64 i) :=
    ⟨_, tab_mem (okB_namesT hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
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
    rcases (BinCheck.img_bytesT hbin hI hii).2 with h | h
    · rw [hb] at h; cases h; rfl
    · exact absurd h hnr
  · rw [mem_modelOf_not hii]
    exact hX _ _ hkept hb
end ExecBytes
end E2E
