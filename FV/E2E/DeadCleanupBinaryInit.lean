import FV.E2E.DeadCleanupExecGot
import FV.E2E.DeadCleanupExecGoodReads
import FV.E2E.LinkArmProgramInitEX
import FV.E2E.LinkArmIniOfCongr

/-!
# The binary-level theorems under the slot-byte oracle (SEM1 #537, executable level (c))

`binary_correctX` / `binary_correct_exec_proven` (`DeadCleanupBinaryGood`,
`DeadCleanupExecProven`) take the reference CLIF run `ClifRun`, whose entry memory carries no
slot-byte oracle (`PlaceAt`): with a program callee with slots (`NeedSlots`) a run that reads an
unwritten slot byte is then stuck, and the theorems say nothing about it (#537). Here the
reference CLIF run is placed with **the machine's own slot table** (`iniB`: `LinkSys.iniOf` of
the linked machine's run from the model state), as `backend_correct_program_initEX`; the
returning runs are covered.

* `iniB`, **`ClifRunB`** (`ClifRun` with `place` under the oracle `iniB`), `sysW`, `kapW` (the
  linked system and budget the proof instantiates), **`InitOk`** (the oracle route's premises:
  the scope conditions `BaseRetOk`, `RetCount`, `HooksKeep` and the determinism premises `DetPRB`,
  `DetTabPRBE`, `DetTabPRBr`, of the system the proof uses), `iniOf_F`, `iniOf_sysS`;
* **`premisesB`** (`premises` with `ClifRunB`), `modelOf_diff`;
* **`binary_correct_init`**: a returning whole-program CLIF run is realised by the linked machine
  from the model state, which has the per-state facts (`RunGoodL`);
* `runGoodL_of_sysS`, `model_init_sysS`, **`binary_correct_exec_init`**: the executable machine
  run from `r` itself refines a returning whole-program CLIF run (`ExecRefines`).

Not covered: a trapping CLIF run under the oracle (no theorem of the oracle route covers traps
yet); with `¬ NeedSlots` the oracle is unused and the old theorems apply.
-/

namespace E2E.DeadCleanupBinary
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck

/-- **The slot table of an outside call of `f` in `r`**: the linked machine's own (`iniOf`), read
off its run of depth `M` from the model state. -/
noncomputable def iniB (I : LinkInput) (B : BaseEnv) (M : Nat) (f : Clif.Function)
    (r : Arm.ArmState) : Clif.SlotInit :=
  (sys I B).std.iniOf M f (modelOf I f r)

/-- **The reference CLIF run under the slot-byte oracle** (`ClifRun` whose slot-placement oracle
is the machine's own table `iniB`, needed only with slotted program callees). -/
structure ClifRunB (I : LinkInput) (B : BaseEnv) (M : Nat) (f : Clif.Function) (r : Arm.ArmState)
    (args : List Clif.Val) (cs : Clif.State) : Prop where
  entry : ClifEntry f args cs
  slots : SlotRel f ((spBody (art I f).af r).toNat + (art I f).af.slotBase) cs.frame.slots
  place : (sys I B).NeedSlots → (sys I B).PlaceAtB cs.mem (spBody (art I f).af r) (iniB I B M f r)

/-- The linked system of an outside call of `f` in `r` the binary-level proofs instantiate
(`binary_correctX`'s). -/
abbrev sysW (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState) : LinkSys :=
  LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)

/-- Its budget (`DeadCleanupStackBound.budget_of`). -/
abbrev kapW (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState) :
    Nat → Clif.Function → Nat :=
  (sysW I B f r).hybrid (DeadCleanupStackBound.budO I) (DeadCleanupStackBound.budMax I)

/-- **The premises of the oracle route** for the linked system `L` with budget `κ`: the scope
conditions `BaseRetOk`, `RetCount`, `HooksKeep` and the determinism of the linked machine
(`DetPRB`, `DetTabPRBE`, `DetTabPRBr`, #701/#713). -/
structure InitOk (L : LinkSys) (κ : Nat → Clif.Function → Nat) : Prop where
  baseRet : L.BaseRetOk
  retCount : ∀ g ∈ L.P.funcs, L.RetCount g
  det : ∀ M, L.std.DetPRB κ M
  detTab : ∀ M, L.std.DetTabPRBE κ M
  detTabR : ∀ M, L.std.DetTabPRBr κ M
  hooks : L.HooksKeep

/-- The machine's own table does not depend on the exterior `F`. -/
theorem iniOf_F (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (LinkSys.ofInputCleanup I B F).std.iniOf = (sys I B).std.iniOf :=
  LinkSys.iniOf_congr rfl rfl rfl fun M g => by
    rw [LinkSys.mach_std, LinkSys.mach_std]; exact mach_F I B F (fun _ => False) M g

/-- **`premises` with the reference CLIF run under the slot-byte oracle** (`ClifRunB`; the stack
premise is the room `StackRoom` only, #581: `StackAvail` also asks `probeBelow ≤ K`, a fact of
the budget). -/
theorem premisesB {I : LinkInput} {B : BaseEnv} {f : Clif.Function} {K M : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hL : (LinkSys.ofInputCleanup I B (worldF I f K r)).Ok) (hf : f ∈ (prog I).funcs)
    {roB : BitVec 64 → Option (BitVec 8)} (hro : ∀ a b, roB a = some b → r.mem a = b)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) :
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackRoom ((art I f).af.frameSize + 16 + K) (modelOf I f r) ∧
    (∀ a, img I a → ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    (∀ a, img I a → (modelOf I f r).mem a = imgMem I a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧ StackArgsAvoid (img I) f.sig args (modelOf I f r) ∧
    Rel.holds ⟨worldF I f K r, fun n => I.syms.lookup n, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sys I B).NeedSlots → (sys I B).PlaceAtB cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))
      (iniB I B M f r)) := by
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL hf
  have hsp := (spv r).isLt
  have hN := ho.stack
  have himg : ∀ a, img I a → (modelOf I f r).mem a = imgMem I a := fun a h => mem_modelOf_img h
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  -- a byte at `sp_body + j` with `j` below the frame drop is in the free stack
  have hbelow : ∀ j < frameDrop (art I f).af,
      StackBelow (frameDrop (art I f).af + K) (spv r) (spBody (art I f).af r + BitVec.ofNat 64 j) ∧
      (spBody (art I f).af r + BitVec.ofNat 64 j - spBody (art I f).af r).toNat = j := by
    intro j hj
    refine ⟨?_, by rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega⟩
    simp only [StackBelow, BitVec.toNat_add, BitVec.toNat_ofNat, hspbN]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨⟨by simp, hL.imgCode f hf _ himg, by rw [r_modelOf]; exact ho.pc,
    by rw [r_modelOf]; exact ho.err, by simp only [xreg]; rw [r_modelOf], fun k hk e => ?_,
    by rw [spv_modelOf]; exact ho.spAligned, hL.fits f hf⟩, ?_, ?_, himg,
    bodyEntry_bodyOf _ _, ?_, ?_, ⟨⟨fun a b hv hb => ?_, fun a n hv => ?_, ho.symbols⟩, ?_, ?_⟩, ?_⟩
  · -- the return address is outside `f`'s code
    obtain ⟨w, hw⟩ : ∃ w, (art I f).fb.words[k]? = some w := ⟨_, Array.getElem?_eq_getElem hk⟩
    apply ho.ra
    rw [e]
    have := codeAddr_word (s := modelOf I f r) (base := (art I f).base) (by simp) hw (i := 0) (by omega)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    exact img_of_codeAddr hL hf this
  · -- the stack
    refine stackRoom_of (by rw [spv_modelOf, ← hd]; exact hN) fun a hc hb => ?_
    rw [spv_modelOf, ← hd] at hb
    exact ho.stackFree a (img_of_codeAddr hL hf hc) hb
  · intro a ha
    rw [spv_modelOf]
    exact ho.stackFree a ha
  · -- the arguments
    intro loc v hm
    have h := ho.args loc v hm
    cases loc with
    | reg x => simp only at h ⊢; rw [regVal_modelOf]; exact h
    | stack off =>
      obtain ⟨hfit, hav, hby⟩ := h
      have hbytes : ∀ k < v.ty.bytes, (modelOf I f r).mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          r.mem (spv r + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := fun k hk => mem_modelOf_not (hav k hk)
      refine ⟨by rw [spv_modelOf]; exact hfit, fun k hk hc => hav k hk ?_, ?_⟩
      · have := img_of_codeAddr hL hf hc
        rwa [spv_modelOf, BitVec.ofNat_add, ← BitVec.add_assoc] at this
      · rw [spv_modelOf, read_mem_bytes_congr _ _ hbytes]; exact hby
  · intro off v hm
    obtain ⟨-, hav, -⟩ := ho.args (.stack off) v hm
    rw [spv_modelOf]; exact hav
  · -- the live CLIF bytes (the body-entry memory is after the stack probes, #581)
    have hni := ((ho.valid a 1 hv).2 0 (by omega)).1
    simp only [Nat.add_zero] at hni
    show probeMem (art I f).af (modelOf I f r) (BitVec.ofNat 64 a) = b
    rw [probeMem_congr (by rw [spv_modelOf]) (mem_modelOf_not hni)]
    exact ho.bytes a b hv hb
  · obtain ⟨hfit, hk⟩ := ho.valid a n hv
    exact ⟨hfit, fun k hkn => not_worldF hL hf hN (hk k hkn).1 (hk k hkn).2⟩
  · -- the slots
    rw [Rel.slotReg, hspb]; exact hr.slots
  · -- the outgoing area: free stack below the slot region
    refine ⟨show (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤ 2 ^ 64 by omega,
      fun j hj => ?_, fun a n hv k hk j hj e => ?_⟩
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb]
      obtain ⟨hb, -⟩ := hbelow j (by omega)
      exact not_worldF_out hL hf hN hj (fun hi => ho.stackFree _ hi hb)
    · change j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase at hj
      rw [hspb] at e
      obtain ⟨hb, ho'⟩ := hbelow j (by omega)
      have := ((ho.valid a n hv).2 k hk).2 (by rw [e]; exact hb)
      rw [e] at this
      unfold SlotArea at this
      omega
  · intro hN'; rw [hspb]; exact hr.place hN'

/-- The model state differs from `r` only at the relocated instruction bytes `R`
(`binary_correct`'s second part). -/
theorem modelOf_diff {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) {r : Arm.ArmState}
    (hX : X.Intact r) (f : Clif.Function) : ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  intro a hne
  by_cases hi : img I a
  · rw [mem_modelOf_img hi] at hne
    rcases (hbin.code a hi).2 with h | h
    · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
    · exact h
  · exact absurd (mem_modelOf_not hi) hne

/-- The budget of an acyclic function is its bound at every depth. -/
theorem kapW_eq {I : LinkInput} (B : BaseEnv) {n : String}
    (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function} (hf : (prog I).func? n = some f)
    (r : Arm.ArmState) (M : Nat) : kapW I B f r M f = DeadCleanupStackBound.bud I f := by
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  have hn' := hn
  unfold DeadCleanupStackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  simp [LinkSys.hybrid, hb, hbud]

/-- **The binary-level theorem under the slot-byte oracle, returning runs** (module doc): as
`binary_correctX` for a returning whole-program CLIF run from the reference entry placed with the
machine's own slot table (`ClifRunB`), under the oracle route's premises (`InitOk`). -/
theorem binary_correct_init {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : DeadCleanupStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOk (sysW I B f r) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.returned vals cm) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    (sys I B).RunGoodL M f (modelOf I f r) := by
  have hB' : BaseOk (sysW I B f r) := baseOk_F hB
  have himgF : ∀ a, (sysW I B f r).Img a → worldF I f (DeadCleanupStackBound.bud I f) r a :=
    fun _ h => .inr h
  have hL := okBCleanup_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  have hfm := (Clif.Program.func?_some hf).1
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premisesB hL hfm hro ho hr
  have hκf := kapW_eq B hn hf r M
  obtain ⟨hA, hG⟩ := backend_correct_program_initEX (sysW I B f r) hL (κ := kapW I B f r)
    (DeadCleanupStackBound.budget_of hbin.ok B (worldF I f (DeadCleanupStackBound.bud I f) r))
    hIO.baseRet hIO.retCount hIO.det hIO.detTab hIO.detTabR hIO.hooks hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf]; exact (DeadCleanupStackBound.budget_of hbin.ok B
      (worldF I f (DeadCleanupStackBound.bud I f) r)).2 M f hfm⟩) (by rw [hκf]; rfl)
    (by rw [hκf]; exact hgfree) himg hbe hargs
    hr.entry hsav hrel (fun hN => by rw [iniOf_F]; exact hpl hN) hrun
  refine ⟨?_, modelOf_diff hbin hX f, runGoodL_F hG⟩
  rw [mach_F I B (fun _ => False) (worldF I f (DeadCleanupStackBound.bud I f) r)]
  exact hA

end E2E.DeadCleanupBinary

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The machine's own table of the system keeping the slots `S` is the plain system's. -/
theorem iniOf_sysS (f : Clif.Function) (r : Arm.ArmState) (S : BitVec 64 → Prop) :
    (sysS I B f r S).std.iniOf = (sys I B).std.iniOf :=
  LinkSys.iniOf_congr rfl rfl rfl fun M g => by
    rw [LinkSys.mach_std, LinkSys.mach_std]; exact mach_sysS f r S M g

/-- **`RunGoodL` of the system keeping the slots `S` gives the plain system's** (the same machine;
a smaller image, whose bytes the model state holds). -/
theorem runGoodL_of_sysS {f : Clif.Function} {r : Arm.ArmState} {S : BitVec 64 → Prop} {M : Nat}
    {c : Arm.ArmState} (h : (sysS I B f r S).RunGoodL M f c) : (sys I B).RunGoodL M f c := by
  intro M' g c' t hR he
  have hR' : (sysS I B f r S).ReachL M f c M' g c' t :=
    LinkSys.reachL_extImg (F := worldFS I f (DeadCleanupStackBound.bud I f) r S) (S := S)
      (m := (modelOf I f r).mem)
      (E2E.DeadCleanupBinary.reachL_F (F := worldF I f (DeadCleanupStackBound.bud I f) r)
        (F' := fun _ => False) hR)
  obtain ⟨X, K, G, gv, heq, hg, himgG, himgS, hblr⟩ :=
    h M' g c' t hR' (by rw [mach_sysS]; exact he)
  have hh : (sysS I B f r S).hooks M' = (sys I B).hooks M' := by
    rw [sysS, LinkSys.hooks_extImg, hooks_F]
  rw [hh] at heq hg
  exact ⟨X, K, G, gv, heq.trans (mach_sysS f r S M' g), hg, fun a ha => himgG a (.inl ha),
    fun a ha => (himgS a (.inl ha)).trans (mem_modelOf_img (f := f) (r := r) ha), hblr⟩

/-- **The model's returning run in the system keeping the slots `S`** (`runGood_sysS` under the
slot-byte oracle): realised by the linked machine, with the per-state facts of that system. -/
theorem model_init_sysS {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hbin : E2E.DeadCleanupBinCheck.BinOk I D file) (hB : BaseOk (sys I B)) {n : String}
    (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOk (sysS I B f r S) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.returned vals cm) ∧
    (sysS I B f r S).RunGoodL M f (modelOf I f r) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).Img a →
      worldF I f (DeadCleanupStackBound.bud I f) r a := fun _ h => .inr h
  have hL0 := okBCleanup_sound hI hB' himgF
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, -, hbe, hargs, hsav, hrel, hpl⟩ := premisesB hL0 hfm hro ho hr
  have hL : (sysS I B f r S).Ok := LinkSys.Ok.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  have hκf := kapW_eq B hn hf r M
  obtain ⟨hd, hsb, hib, hsz⟩ := frame_facts hL0 hfm
  have hN := ho.stack
  have hN' : frameDrop (art I f).af + DeadCleanupStackBound.bud I f ≤ (spv r).toNat := hN
  have hsp := (spv r).isLt
  have hspbN : (spBody (art I f).af r).toNat = (spv r).toNat - frameDrop (art I f).af :=
    (off_toNat 0 (spv r) _ (by omega)).2.2
  have hspb : spv (bodyOf (art I f).af (modelOf I f r)) = spBody (art I f).af r := by
    rw [spv_bodyOf, spv_modelOf]; rfl
  refine (fun hAG => ⟨by rw [← mach_sysS f r S]; exact hAG.1, hAG.2⟩)
    (backend_correct_program_initEX (sysS I B f r S) hL (κ := kapW I B f r)
    ((DeadCleanupStackBound.budget_of hI B (worldF I f (DeadCleanupStackBound.bud I f) r)).extImg _ _ _)
    hIO.baseRet hIO.retCount hIO.det hIO.detTab hIO.detTabR hIO.hooks hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf]; exact (DeadCleanupStackBound.budget_of hI B
      (worldF I f (DeadCleanupStackBound.bud I f) r)).2 M f hfm⟩) (by rw [hκf]; rfl)
    (fun a ha => ?_) (fun a _ => rfl) hbe hargs
    hr.entry (fun off v hm k hk hx => ?_)
    ⟨⟨hrel.1.bytes, fun a n hv => ?_, hrel.1.symbols⟩, hrel.2.1, hrel.2.2.1, fun j hj => ?_,
      hrel.2.2.2.2⟩ (fun hN => by rw [iniOf_sysS]; exact hpl hN) hrun)
  · rw [hκf]
    rcases ha with ha | ha
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

/-- **The binary theorem about the executable's own words under the slot-byte oracle, returning
runs** (module doc): under `binary_correct_exec_proven`'s premises, with the reference CLIF run
placed with the machine's own slot table (`ClifRunB`) and the oracle route's premises for the
system keeping the GOT slots (`InitOk`), the executable machine run from `r` refines a returning
whole-program CLIF run. -/
theorem binary_correct_exec_init {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOk (sysS I B f r (GotSlot I file)) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.returned vals cm) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨hA, hgS⟩ := model_init_sysS hI hbin hB hn hf M hX ho hav hr hIO hrun
  have hG := runGoodL_of_sysS hgS
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  have hB'' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL0 := okBCleanup_sound hI hB'' fun _ h => .inr h
  obtain ⟨hent, -⟩ := premisesB hL0 hfm hro ho hr
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  have hra : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hent.raOutside
  have hreads : RunReadsN I B file M f (modelOf I f r) := fun M' g t hR he => by
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm hG (raNotSecond_top (hF f hfm) hra)
    have hRL' : (sysS I B f r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t :=
      LinkSys.reachL_extImg (F := worldFS I f (DeadCleanupStackBound.bud I f) r (GotSlot I file))
        (S := GotSlot I file) (m := (modelOf I f r).mem)
        (E2E.DeadCleanupBinary.reachL_F (F := worldF I f (DeadCleanupStackBound.bud I f) r)
          (F' := fun _ => False) hRL)
    have hg := reachN_mem hR hfm
    exact ⟨insn_of_good hI hcm hF hg (hG _ _ _ _ hRL he),
      got_of_good hI hbin hgot hX hg (hF g hg) (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))⟩
  exact exec_of_modelN hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside
    (modelOf_diff hfacts hX f)
    (runOkSN_of_n hI hcm hF hH hfm
      (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra hG hreads)) hA

end E2E.DeadCleanupExecBytes
