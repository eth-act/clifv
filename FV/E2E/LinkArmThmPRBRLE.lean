import FV.E2E.LinkArmTableECall
import FV.E2E.LinkArmCountPRBSucc

/-!
# The linking statement with the prefix-closed table (SEM1 #537, #680 (3), fix of #700, step 4)

`ThmPRBRL` takes the caller-side table `TableOf`, which presupposes that the machine's program
callees return (#700). `ThmPRBRLE` takes the prefix-closed `TableOfE` instead (it implies
`ThmPRBRL`, `ThmPRBRLE.toThmPRBRL`). The callees keep the old statement: a callee whose CLIF run
returns gets the old `TableOf` at its canonical entry from `ThmPRBRLE` one level down
(`tableOf_canon_of_E`), so the machine semantics of a call (`progXBT`, whose condition asks for
the canonical `TableOf`) and every lemma about it stay as they are.

* `progBase_of_callsTo`: at a program call of `g`'s code with `g`'s program, the program base is
  `g`'s;
* **`tabUpTo_count_E`**: a table and a prefix-closed table of the same prefix have the same count
  (each callee of the table returns, so the prefix-closed table's return clause applies);
* **`tabUpTo_of_E`**: a prefix-closed table is a table when every state after a step of the prefix
  has no error (`callsTo_ret`: each callee returned);
* `ThmPRBRLE`, `ThmPRBRLE.toThmPRBRL`; `DetTabPRBE` (`DetTabPRB` for `TableOfE`: a premise until
  the determinism theorems land, #704/#705);
* `tableOf_of_retAtN`: a run with a return at `n` and a table up to `n` has `TableOf`;
* **`canonEntry`**: the canonical callee entry of `progCallPRBRL` (its proof's first half: the
  callee's `WorldEntryB`, `MachEntryPR` with its own prophecies, `RaOk`, the returning run one
  level down);
* **`tableOf_canon_of_E`**: the canonical callee run's `TableOf` from its `TableOfE` and
  `ThmPRBRLE` one level down.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The program base at a call of `g`'s code** with `g`'s program loaded. -/
theorem progBase_of_callsTo (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    {t u : Arm.ArmState} (hct : L.CallsTo g t h)
    (hprog : u.program = (L.A g).fb.program (L.A g).base) : progBase u = (L.A g).base := by
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨x, hx⟩ : ∃ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some x := by
    rcases hct with ⟨n, hn, -⟩ | ⟨⟨x, hx⟩, -⟩
    · exact ⟨_, hn⟩
    · exact ⟨_, hx⟩
  unfold insnAt at hx
  split at hx
  · rename_i hex
    obtain ⟨j, i, t', hj, -⟩ := hex
    obtain ⟨_, w, -, hk⟩ := FnAsm.layout_word hc.layout hlm hj rfl
    have hne : (L.A g).fb.words.toList ≠ [] := by
      intro h1
      have : (L.A g).fb.words.size = 0 := by simpa using congrArg List.length h1
      simp [this] at hk
    exact progBase_eq (by rw [hprog]; rfl) hne
  · cases hx

/-- **A table and a prefix-closed table of a prefix have the same count.** -/
theorem tabUpTo_count_E {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {b b' : Nat → Nat → BitVec 8} {k k' N e e' : Nat}
    (h : L.TabUpTo M g s b k N e) (h' : L.TabUpToE M g s b' k' N e') : e = e' := by
  cases M with
  | zero => exact h.1.trans h'.symm
  | succ M =>
    obtain ⟨E, rfl, hE⟩ := h
    obtain ⟨E', rfl, hE'⟩ := h'
    refine sumTo_congr_calls N fun i hi hpc => ?_
    by_cases hcall : ∃ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h
    · obtain ⟨h, hch⟩ := hcall
      obtain ⟨-, hle, N₁, hr₁, hm₁, ht₁⟩ := (hE i hi hpc).2 h hch
      obtain ⟨-, hle', -, ht₂⟩ := (hE' i hi hpc).2 h hch
      have := L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ ht₁ (ht₂ N₁ hr₁ hm₁)
      omega
    · have hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h := fun h hc => hcall ⟨h, hc⟩
      rw [(hE i hi hpc).1 hn, (hE' i hi hpc).1 hn]

/-- **A prefix-closed table is a table** when the prefix runs `g`'s program and every state after
one of its steps has no error: each callee of the prefix returned (`callsTo_ret`). -/
theorem tabUpTo_of_E (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    ∀ (M : Nat) (s : Arm.ArmState) (b : Nat → Nat → BitVec 8) (k N e : Nat),
    (∀ i < N, (runX (L.mach M g) i s).program = (L.A g).fb.program (L.A g).base) →
    (∀ i < N, Arm.r .ERR (runX (L.mach M g) (i + 1) s) = .None) →
    L.TabUpToE M g s b k N e → L.TabUpTo M g s b k N e
  | 0, s, _, _, _, _, hprog, herr, h => ⟨h, fun i hi h' hc => by
      have hr := herr i hi
      rw [runX_add _ i 1] at hr
      obtain ⟨M', hM, -⟩ := L.callsTo_ret hc (L.progBase_of_callsTo hL hg hc (hprog i hi)) hr
      exact Nat.succ_ne_zero M' hM.symm⟩
  | M + 1, s, b, k, N, e, hprog, herr, h => by
    obtain ⟨E, he, hE⟩ := h
    refine ⟨E, he, fun i hi hpc => ⟨(hE i hi hpc).1, fun h hch => ?_⟩⟩
    obtain ⟨hsb, hle, -, hret⟩ := (hE i hi hpc).2 h hch
    have hr := herr i hi
    rw [runX_add _ i 1] at hr
    obtain ⟨M', hM, N₁, hr₁, hm₁⟩ :=
      L.callsTo_ret hch (L.progBase_of_callsTo hL hg hch (hprog i hi)) hr
    obtain rfl : M = M' := Nat.succ.inj hM
    exact ⟨hsb, hle, N₁, hr₁, hm₁, hret N₁ hr₁ hm₁⟩

/-- **`ThmPRBRL` with the prefix-closed table** (`TableOfE` at the entry). -/
def ThmPRBRLE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s) →
    RaOk (L.A g) (ra - 4) →
    L.TableOfE M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (n e : Nat),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
      PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
      L.TabUpTo M g s ini.bytes ini.next n e ∧ (L.NeedSlots → Clif.NextAdv cs.mem.leave cm' e)

/-- `ThmPRBRLE` gives `ThmPRBRL` (`TableOf → TableOfE`). -/
theorem ThmPRBRLE.toThmPRBRL {M : Nat} (h : L.ThmPRBRLE κ M) : L.ThmPRBRL κ M :=
  fun g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun =>
    h g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra (L.tableOfE_of htab) hrun

/-- **`DetTabPRB` for the prefix-closed table**: under `progCallPRB`'s premises a call state `t`
compatible with the canonical state whose callee run has `ini'`'s prefix-closed table gives the
canonical callee run the same prefix-closed table. -/
def DetTabPRBE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ (n : String) (h : Clif.Function), L.P.func? n = some h → (∃ g ∈ L.P.funcs, L.Callee g h) →
    ∀ (F : BitVec 64 → Prop), (∀ a, L.Img a → F a) →
    ∀ (uses : List CV) (w : Arm.ArmState), Arm.r .ERR w = .None → (spv w).toNat % 16 = 0 →
    frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat →
    (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a) →
    ∀ (vals : List Clif.Val) (cm : Clif.Mem) (cs : Clif.State) (rvals : List Clif.Val)
      (cm' : Clif.Mem) (ini : Clif.SlotInit),
    MemRel F L.syms cm w → ArgsAt h.sig vals uses w → StackArgsAvoid F h.sig vals w →
    (L.NeedSlots → L.PlaceAtB cm (spv w) ini) →
    (L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a)) →
    Clif.initState L.P n vals cm = .ok cs → L.crun M cs = .returned rvals cm' →
    ∀ t, L.CallerOk F h uses w t →
      (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (L.canon h uses w)) →
      (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
        t.mem a = (L.canon h uses w).mem a) →
      L.TableOfE (M - 1) h (enterAt (L.A h) t) (calleeIni h ini) →
      L.TableOfE (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini)

/-- **A run that returns at `n` with a table up to `n` has `TableOf`** (the prefixes before the
return are at most `n` long). -/
theorem tableOf_of_retAtN {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {ini : Clif.SlotInit}
    {n e : Nat} (hr : L.RetAt g s (runX (L.mach M g) n s))
    (ht : L.TabUpTo M g s ini.bytes ini.next n e) : L.TableOf M g s ini := fun N hN => by
  rcases Nat.lt_or_ge n N with hlt | hle
  · exact absurd hr (hN n hlt)
  · exact L.tabUpTo_mono ht hle

/-- The callee oracle of an advanced oracle, as a structure. -/
theorem calleeIni_adv_eq (h : Clif.Function) (ini : Clif.SlotInit) {x y : Nat} (hx : x = y) :
    calleeIni h (ini.adv x) = ⟨ini.bytes, ini.next + y + slotted h⟩ := by
  rw [show calleeIni h (ini.adv x) =
      ⟨(calleeIni h (ini.adv x)).bytes, (calleeIni h (ini.adv x)).next⟩ from rfl,
    calleeIni_bytes, calleeIni_next]
  simp only [Clif.SlotInit.adv]
  rw [hx]

/-- **The canonical callee entry** of `progCallPRBRL` (module doc). -/
theorem canonEntry (hL : L.Ok) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F L.syms cm w)
    (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAtB cm (spv w) ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') :
    ∃ (Fh G : BitVec 64 → Prop) (w₀ : Arm.ArmState) (m : Nat),
      L.WorldEntryB κ (M - 1) h Fh vals cs w₀ (calleeIni h ini) ∧
      L.MachEntryPR κ (M - 1) h Fh G (Arm.r .PC (L.canon h uses w) + 4)
        (enterAt (L.A h) (L.canon h uses w)) w₀
        (prophOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base (enterAt (L.A h) (L.canon h uses w)))
        (prophStOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base
          (enterAt (L.A h) (L.canon h uses w))) ∧
      RaOk (L.A h) (Arm.r .PC (L.canon h uses w) + 4 - 4) ∧
      Clif.runLoop (L.envR (M - 1) h) L.P.bare m cs = .returned rvals cm' := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  have hslotB : (L.A h).af.slotBase = (RAFrame.compute (L.A h).vcp (L.A h).rf).size :=
    (lowerRFunc_ok hc.alloc).1.2.1
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  -- the callee's entry (`initState_memB` with program callees with slots, else no slots)
  have hentry : cs.frame.slots = h.slots.map (fun p => (p.1,
        (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
          ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0))) ∧
      cs.mem.symbols = cm.symbols ∧
      (∀ x ∈ cs.mem.allocs, x ∈ cm.allocs ∨ ∃ p ∈ h.slots,
        x = ⟨(spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
          ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0), p.2.size, false⟩) ∧
      (∀ a b, cs.mem.bytes a = some b →
        (cm.bytes a = some b ∧ ∀ p ∈ h.slots,
          ¬ ((spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
              ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) ≤ a ∧
            a < (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
              ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) + p.2.size)) ∨
        (L.NeedSlots ∧ L.SlotByte h (spv w) a ∧ b = ini.bytes (ini.next + 1) a)) ∧
      (L.NeedSlots → L.PlaceAtB cs.mem (spv w - BitVec.ofNat 64 (frameDrop (L.A h).af))
        (calleeIni h ini)) := by
    by_cases hN : L.NeedSlots
    · obtain ⟨h1, h2, h3, h4, h5⟩ := L.initState_memB hpf hinit (hpl hN)
      refine ⟨h1, h2, h3, fun a b hb => ?_, fun _ => h5⟩
      rcases h4 a b hb with h4 | ⟨p, hp, hlo, hhi, rfl⟩
      · exact .inl h4
      · exact .inr ⟨hN, ⟨p, hp, hlo, hhi⟩, rfl⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := L.initState_mem hpf hinit (c := spv w) (.inl (hsl0 hN))
      exact ⟨h1, h2, h3, fun a b hb => .inl (h4 a b hb), fun h' => absurd h' hN⟩
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := hentry
  have hsz_le := size_le_frameSize hc.alloc
  have hfits : ∀ p ∈ h.slots, ∃ off, (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hL.slotFits g hg h hcg
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the run of the program without functions (program callees: the callee runs one level down)
  obtain ⟨m, hm⟩ := hR.link M hM h hh cs (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
    (L.envR (M - 1) h) rfl rfl (fun _ hn => L.envR_of (.inl hn)) (L.envR_link hL.names)
    (by rw [hrun]; intro _ e; cases e) (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon hL hh himgF uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  -- the callee's outgoing area (in the caller's dead stack) is outside the callee's `F`
  let ib := (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase
  let spb := spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)
  let sz := (RAFrame.compute (L.A h).vcp (L.A h).rf).size
  let Fh : BitVec 64 → Prop := fun a =>
    F a ∧ ¬ OutAt ib spb a ∧ ¬ SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a
  have hib_le : ib ≤ sz := intBase_le_size _ _
  have hspb : spb.toNat = (spv w).toNat - frameDrop (L.A h).af := hB
  have hlt := (spv w).isLt
  have hout_reg : ∀ a, OutAt ib spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  -- the callee's slot region (in the caller's dead stack) is outside the callee's `F`
  have hslot_reg : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hslot_F : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a → F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
  -- a slot byte of the callee is in its slot region
  have hslot_at : ∀ a, L.SlotByte h (spv w) a →
      SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb (BitVec.ofNat 64 a) := by
    intro a ⟨p, hp, hlo, hhi⟩
    obtain ⟨off, hoff, hle⟩ := hfits p hp
    simp only [hoff, Option.getD_some] at hlo hhi
    have e : (BitVec.ofNat 64 a).toNat = a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by rw [e]; omega, by rw [e]; omega⟩
  have hspb_add : ∀ j < ib, OutAt ib spb (spb + BitVec.ofNat 64 j) := by
    intro j hj
    have e : (spb + BitVec.ofNat 64 j).toNat = spb.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), hspb]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  have hOut : ∀ (u : Arm.ArmState), spv u = spb →
      (∀ a n, cs.mem.valid a n = true → ∀ k < n, ¬ OutAt ib spb (BitVec.ofNat 64 (a + k))) →
      OutRel Fh ib cs.mem u := by
    intro u hu hv
    refine ⟨by omega, fun j hj hfh => hfh.2.1 (hu ▸ hspb_add j hj), fun a n hva k hk j hj e => ?_⟩
    rw [hu] at e
    exact hv a n hva k hk (e ▸ hspb_add j hj)
  -- the live allocations of the callee's entry: the caller's, and its slots in its slot region
  have hcsv : ∀ a n, cs.mem.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
      ¬ Fh (BitVec.ofNat 64 (a + k)) ∧ ¬ OutAt ib spb (BitVec.ofNat 64 (a + k)) := by
    intro a n hv
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨x, hx, hcx⟩ := hv
    rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a n = true := List.any_eq_true.mpr ⟨x, hx', hcx⟩
      obtain ⟨h1, h2⟩ := hmr.valid a n hv'
      exact ⟨h1, fun k hk => ⟨fun hf => h2 k hk hf.1, fun ho => h2 k hk (hout_F _ ho).1⟩⟩
    · obtain ⟨off, hoff, hle⟩ := hfits p hp
      simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq, hoff,
        Option.getD_some] at hcx
      refine ⟨by omega, fun k hk => ?_⟩
      have e : (BitVec.ofNat 64 (a + k)).toNat = a + k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨fun hf => hf.2.2 ⟨by rw [e]; omega, by rw [e]; omega⟩,
        fun ⟨o1, o2⟩ => by rw [e] at o1 o2; omega⟩
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's and
  -- holding the table's slot bytes
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      (L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
        Arm.read_mem (BitVec.ofNat 64 a) u = ini.bytes (ini.next + 1) a) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu hsu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · rcases hby' a b hb with ⟨hb', hnot⟩ | ⟨hN, hsb, rfl⟩
      · refine hbu a b ?_ hb'
        simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
        obtain ⟨x, hx, hcx⟩ := hv
        rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
        · exact ⟨x, hx', hcx⟩
        · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
          exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
      · exact hsu hN a hsb
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntryB κ (M - 1) h Fh vals cs w₀ (calleeIni h ini) := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' hN⟩
    · refine hRel w₀ hspw₀ ?_ (fun a b hv hb => ?_) (fun hN a hsb => ?_)
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)
      · rw [hslotb hN a hsb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg (fun hi => (hslot_F _ (hslot_at a hsb)).2 hi)]
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        simp only
        have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
          have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          rw [if_pos hfr, spv_enterAt, hsp0] at this
          exact this
        rw [hx29, fp_off_eq]
        refine ⟨fun k hk hf => hsav off v hmem k hk hf.1, ?_⟩
        rw [show Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w₀ =
            Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w from
          read_mem_bytes_congr _ _ (fun k hk => by
            simp only [w₀, mem_bodyOf, mem_enterAt]
            rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmem k hk (himgF _ hi))])]
        exact hargs.2.2 off v hmem
      | reg r =>
        obtain ⟨i, hr, hv⟩ := reg_zip _ _ hi
        have hlen := hargs.2.1.1
        obtain ⟨u, hu⟩ : ∃ u, uses[i]? = some u := by
          have hi' : i < uses.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
          exact ⟨uses[i]'hi', List.getElem?_eq_getElem _⟩
        have hvh := hargs.2.1.2 i v u hv hu
        have hrA : r.isArgReg = true := harg r (List.mem_of_getElem? hr)
        simp only
        rw [show regVal w₀ r = regVal (placeArgs (regLocs h.sig) uses (L.withImg w)) r by
          simp only [w₀]; rw [regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA, L.regVal_canon _ _ _ hrA],
          placeArgs_regVal _ _ _ hnd harg hr hu]
        refine vHolds_setVal ?_ hvh
        have hty := hce.sig
        have hvmem : v ∈ vals := List.of_mem_zip hmem |>.2
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
        have e := congrArg (·[j]?) hty
        simp only [List.getElem?_map, hj, Option.map_some] at e
        cases hp : h.sig.params[j]? with
        | none => rw [hp] at e; cases e
        | some p =>
          rw [hp] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]; exact hwid p (List.mem_of_getElem? hp)
    · rw [hspw₀, hB]; omega
    · intro a ha
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      have hd := hdead a ⟨by omega, by omega⟩
      exact ⟨⟨hd.1, fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega,
        fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega⟩, hd.2⟩
    · rw [hspw₀, hB, hdrop]; omega
  -- the callee's activation from a caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
  have hcode : ∀ t, ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun t a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : ∀ t w₀', spv t = spv w → Arm.r .ERR t = .None →
      (∀ a, L.Img a → t.mem a = L.imgMem a) →
      BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' →
      L.MachEntry κ (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀' := by
    intro t w₀' hst herrt himgt hbw
    have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
    have hFrame : frameWG (κ (M - 1) h) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
        (L.A h).af G (enterAt (L.A h) t) = Fh := by
      funext a
      apply propext
      rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le (size_le_frameBody hc.alloc), ← hdrop, hspt]
      constructor
      · rintro (⟨hb, hno, hns⟩ | hc | hg)
        · exact ⟨(hdead a hb).1, hno, hns⟩
        · exact ⟨himgF a (hcode t a hc), fun ho => (hout_F a ho).2 (hcode t a hc),
            fun hs => (hslot_F a hs).2 (hcode t a hc)⟩
        · exact ⟨hg.1, fun ho => hg.2 (hout_reg a ho), fun hs => hg.2 (hslot_reg a hs)⟩
      · intro ⟨hF, hno, hns⟩
        by_cases hb : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
        · exact .inl ⟨hb, hno, hns⟩
        · exact .inr (.inr ⟨hF, hb⟩)
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact himgt a ha) k wd hk, by simp, ?_, x30_enterAt _ _, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, hFrame,
      fun a ha => ⟨himgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact himgt a ha, hbw⟩
    · rw [r_enterAt _ _ (by simp) (by simp)]; exact herrt
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode t a ha)
    · rw [hspt]; exact ha.2
  -- the canonical entry: a `MachEntryPR` activation with the prophecies of its own run
  have herrc : Arm.r .ERR cn = .None := by rw [hcOk.world.1 _ (by simp [Masked])]; exact herr
  have hbw0 : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) cn) w₀ :=
    ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
      (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
      fun a _ => by simp [w₀], by simp [w₀]⟩
  have hME0 : L.MachEntryPR κ (M - 1) h Fh G (Arm.r .PC cn + 4) (enterAt (L.A h) cn) w₀
      (prophOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base (enterAt (L.A h) cn))
      (prophStOf (L.mach (M - 1) h) (L.A h).fa (L.A h).base (enterAt (L.A h) cn)) :=
    ⟨⟨hME cn w₀ hsp0 herrc hcOk.img hbw0, prophOk_prophOf _ _ _ _ _ _⟩,
      fun _ hc _ _ _ _ => by rw [prophStOf_call hc]⟩
  exact ⟨Fh, G, w₀, m, hWE, hME0, by rw [BitVec.add_sub_cancel]; exact hcOk.ra, hm⟩

/-- **The canonical callee run's `TableOf` from its `TableOfE`** (module doc): `ThmPRBRLE` one
level down at the canonical entry (`canonEntry`) returns with a table up to the return. -/
theorem tableOf_canon_of_E (hL : L.Ok) [hR : L.CrunOk] {M : Nat} (hM : 0 < M)
    (ih : L.ThmPRBRLE κ (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F L.syms cm w)
    (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAtB cm (spv w) ini)
    (hslotb : L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm')
    (htab : L.TableOfE (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini)) :
    L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini) := by
  obtain ⟨Fh, G, w₀, m, hWE, hME, hra, hm⟩ := L.canonEntry hL hM hpf hcal himgF herr hal hroom
    hdead hmr hargs hsav hpl hslotb hinit hrun
  have hh : h ∈ L.P.funcs := (Clif.Program.func?_some hpf).1
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hret0, -, htab0, -⟩ :=
    ih h hh Fh vals cs w₀ m rvals cm' (calleeIni h ini) G _ _ hWE hME hra htab hm
  exact L.tableOf_of_retAtN (L.retAt_of_actRet hME.entryP.entry hret0) htab0

end LinkSys

end E2E
