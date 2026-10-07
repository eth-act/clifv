import FV.E2E.LinkArm
import FV.E2E.LinkWorldX

/-! # The per-state facts of the linked machine's runs (L3 (c))

`backend_correct_program_budgetX` is `backend_correct_program_budget` with, for a returning or
trapping outcome, the per-state facts (`actGoodX`, the register-level `RL.GoodX`) of every state
of the run whose step ends without error (`RunGoodL`): the states of the entry activation before
its return (`ReachL.act`) and those of the activations nested through its calls
(`ReachL.nest`). The facts of the entry activation's own states come from
`regLevelCorrect_worldX`'s trace; a nested activation is a callee run from a call state, whose
`RL.GoodX.call` gives the premise of the callee contract (`RL.CallPre`), from which the linking
statement one level down (`ThmG`) gives the callee's states their facts. -/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The activation of `a` entered at `c` has returned in `t` (`ExecBytes.Returned`). -/
def RetL (a : Art) (c t : Arm.ArmState) : Prop :=
  Arm.r .PC t = xreg 30 c ∧ Arm.r .ERR t = .None ∧ t.program = a.fb.program a.base ∧ spv t = spv c

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- `ExecBytes.CallsAt` for a LinkSys. -/
def CallsAtL (g : Clif.Function) (s : Arm.ArmState) (h : Clif.Function) : Prop :=
  (∃ n, insnAt (L.A g).fa (progBase s) (Arm.r .PC s) = some (.bl n) ∧ L.P.func? n = some h) ∨
  ((∃ x, insnAt (L.A g).fa (progBase s) (Arm.r .PC s) = some (.blr x)) ∧
    (blrTarget s).bind (symCallee L.Xb L.P) = some h)

/-- States of the activation of `g` at depth `M` entered at `c` before its return, and of the
activations nested through calls whose step ends without error; the last three indices: the
state's own activation (function, depth, entry) and the state. -/
inductive ReachL (L : LinkSys) :
    Nat → Clif.Function → Arm.ArmState → Nat → Clif.Function → Arm.ArmState → Arm.ArmState → Prop
  | act {M g c k} : (∀ j ≤ k, ¬ RetL (L.A g) c (runX (L.mach M g) j c)) →
      L.ReachL M g c M g c (runX (L.mach M g) k c)
  | nest {M g c k h M' g' c' t} :
      (∀ j ≤ k, ¬ RetL (L.A g) c (runX (L.mach (M + 1) g) j c)) →
      L.CallsAtL g (runX (L.mach (M + 1) g) k c) h →
      Arm.r .ERR (runX (L.mach (M + 1) g) (k + 1) c) = .None →
      L.ReachL M h (enterAt (L.A h) (runX (L.mach (M + 1) g) k c)) M' g' c' t →
      L.ReachL (M + 1) g c M' g' c' t

/-- At a `blr` of `g` at `t` whose target is the function `h` of `P`, the call is one through a
register `tv` of `g`'s VCode by which `g` may enter `h` (`BlrTo`). -/
def BlrAt (g : Clif.Function) (t : Arm.ArmState) : Prop :=
  ∀ x h, insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some (.blr x) →
    (blrTarget t).bind (symCallee L.Xb L.P) = some h →
    ∃ info tv, (L.A g).vcp.CallSite info ∧ info.dest = .reg (.vreg tv .int) ∧ L.BlrTo g tv h

/-- The per-state facts at a state `t` of the activation of `g` at depth `M` entered at `c`, with
the code image `Img` among the kept addresses `G`, holding `imgMem` at the entry, and the callee
of a `blr` one `g` may enter through the call's register (`BlrAt`). -/
def GoodAt (M : Nat) (g : Clif.Function) (c t : Arm.ArmState) : Prop :=
  ∃ X K G gv, ArmStepX X (L.hooks M) (L.A g).fa = L.mach M g ∧
    actGoodX (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (L.A g).base c X
      (L.hooks M) K G gv t ∧
    (∀ a, L.Img a → G a) ∧ (∀ a, L.Img a → c.mem a = L.imgMem a) ∧ L.BlrAt g t

/-- **Every state of the run whose step ends without error has the per-state facts.** -/
def RunGoodL (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g c' t, L.ReachL M f c M' g c' t → Arm.r .ERR (L.mach M' g t) = .None → L.GoodAt M' g c' t

/-- **The per-state part of the linking statement at depth `M`**: for the activations of
`LinkSys.Thm` (ordinary and non-interference), every state of the run whose step ends without
error has the per-state facts. -/
def ThmG (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem), L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
      (∀ G ra s, L.MachEntry κ M g F G ra s w₀ → L.RunGoodL M g s) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntry κ M g F G ra s w₀' → L.RunGoodL M g s)

/-- **The linking statement with the per-state facts**: `Thm` and `ThmG`. -/
def ThmX (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop := L.Thm κ M ∧ L.ThmG κ M


/-! ## The callee's states -/

/-- The instruction at an instruction line of a laid-out function, in a state holding its
program. -/
theorem insnAt_ofLine {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) {u : Arm.ArmState} (hprog : u.program = fb.program base)
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t)) :
    insnAt fa (progBase u) (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)) = some x := by
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word hl hm hj rfl
  have hne : fb.words.toList ≠ [] := by
    intro h
    have : fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase u = base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hl
  rw [hb]
  exact insnAt_line (by omega) hj

/-- The register-level activation of `g` at depth `M` entered in `s` (keeping `G`, exterior `F`)
that `thm_of` instantiates the register-level theorem with. -/
noncomputable def actRL (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (s : Arm.ArmState) : RL :=
  ⟨(L.A g).vcp, (L.A g).rf, (L.A g).af, (L.A g).fa, (L.A g).fb, {}, (L.A g).base, s,
    L.X κ M g F, L.hooks M, {}, κ M g, G, GotV (L.A g).vcp⟩

/-- **`progCall`'s per-state facts**: from every caller state compatible with `w`
(`CallerOk`), every state of the callee's run whose step ends without error has the per-state
facts (from `ThmG` one level down, for the callee activation `progCall` builds). -/
theorem progCallG (hL : L.Ok) {M : Nat} (hM : 0 < M) (ihG : L.ThmG κ (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    (hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize) ∨ L.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : Clif.runLoop L.base L.P M cs = .returned rvals cm') :
    ∀ t, L.CallerOk F h uses w t → L.RunGoodL (M - 1) h (enterAt (L.A h) t) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  have hcase : h.slots = [] ∨ L.PlaceAt cm (spv w) := by
    by_cases hN : L.NeedSlots
    · exact .inr (hpl hN)
    · exact .inl (hsl0 hN)
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := L.initState_mem hpf hinit hcase
  have hslotB : (L.A h).af.slotBase = (RAFrame.compute (L.A h).vcp (L.A h).rf).size :=
    (lowerRFunc_ok hc.alloc).1.2.1
  have hsz_le := size_le_frameSize hc.alloc
  have hfits : ∀ p ∈ h.slots, ∃ off, (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize := by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hL.slotFits g hg h hcg
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the run of the program without functions (program callees at most `M - 1` steps)
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) (M - 1) hL.names hh
    hL.free (hL.indScope h hh) (hL.subset h hh).externCalls (hL.subset h hh).tryExterns
    (E := L.envR (M - 1) h) rfl rfl (fun _ hn => L.envR_of (.inl hn))
    (L.envR_link hL.names) M cs (by omega) (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
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
    F a ∧ ¬ OutAt ib spb a ∧ ¬ SlotAt sz (L.A h).af.frameSize spb a
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
  have hslot_reg : ∀ a, SlotAt sz (L.A h).af.frameSize spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hslot_F : ∀ a, SlotAt sz (L.A h).af.frameSize spb a → F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
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
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · obtain ⟨hb', hnot⟩ := hby' a b hb
      refine hbu a b ?_ hb'
      simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
      obtain ⟨x, hx, hcx⟩ := hv
      rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
      · exact ⟨x, hx', hcx⟩
      · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
        exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntry κ (M - 1) h Fh vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' (hpl hN)⟩
    · refine hRel w₀ hspw₀ ?_ fun a b hv hb => ?_
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)
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
  obtain ⟨hallG, hniG⟩ := ihG h hh Fh vals cs w₀ m rvals cm' hWE hm
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
      rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le hsz_le, ← hdrop, hspt]
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
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
    rw [if_pos hfr, spv_enterAt, hsp0] at this
    exact this
  have key2 : L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
      SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
      (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
      MemRel F L.syms cm t →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) →
      L.RunGoodL (M - 1) h (enterAt (L.A h) t) := by
    intro hN Z t hFZ hZ himgt hregt hmt hstkt
    have hst : spv t = spv w := hZ.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [hZ.1 _ (by simp [Masked])]; exact herr
    let w₀' := bodyOf (L.A h).af (enterAt (L.A h) t)
    let D : BitVec 64 → Prop := fun a => Z a ∧ ¬ Fh a
    have hspw₀' : spv w₀' = spb := by
      simp only [w₀']; rw [spv_bodyOf, spv_enterAt, hst]
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' :=
      ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
        (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
        fun a _ => by simp [w₀'], by simp [w₀']⟩
    have hrel' : RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem w₀' := by
      refine hRel w₀' hspw₀' ?_ fun a b hv hb => ?_
      · simp only [w₀']
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact herrt
      · have := hmt.bytes a b hv hb
        simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf, mem_enterAt] at this ⊢
        exact this
    have hsw : SameWorld (fun a => Fh a ∨ D a) w₀ w₀' := by
      refine ⟨fun f hf => ?_, fun a ha => ?_, by simp [w₀, w₀']⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have e1 := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          have e2 := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
          simp only [xreg] at e1 e2
          rw [e1, e2, spv_enterAt, spv_enterAt, hsp0, hst, if_pos hfr, if_pos hfr]
        by_cases h31 : f = .GPR 31#5
        · subst h31
          show spv w₀ = spv w₀'
          rw [hspw₀, hspw₀']
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
        rw [r_bodyOf _ _ h29 h31, r_bodyOf _ _ h29 h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
          hcOk.world.1 f hf, hZ.1 f hf]
      · have hnZ : ¬ Z a := fun hz => by
          by_cases hf : Fh a
          · exact ha (.inl hf)
          · exact ha (.inr ⟨hz, hf⟩)
        simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
        rw [hcOk.world.2.1 a (fun hf => hnZ (hFZ a hf)), hZ.2.1 a hnZ]
    have hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf h.sig).zip vals →
        regVal w₀' r = regVal w₀ r := by
      intro r v hm
      have hrl : r ∈ regLocs h.sig :=
        List.mem_filterMap.mpr ⟨.reg r, (List.of_mem_zip hm).1, rfl⟩
      have hrA := harg r hrl
      simp only [w₀, w₀']
      rw [regVal_bodyOf _ _ hrA, regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA,
        regVal_enterAt _ _ hrA, hregt r hrl]
    have hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) := by
      intro off v hm k hk
      rw [hx29, fp_off_eq]
      have hnF := hsav off v hm k hk
      simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
      rw [hstkt off v hm k hk, hcOk.world.2.1 _ hnF]
    exact hniG hN D w₀' hrel' hsw hreg hstk G (Arm.r .PC t + 4)
      (enterAt (L.A h) t) (hME t w₀' hst herrt himgt hbw)
  intro t ht
  by_cases hN : L.NeedNI
  · refine key2 hN F t (fun _ h => h) ht.world ht.img ht.regs ⟨fun a b hv hb => ?_,
      hmr.valid, hmr.symbols⟩ fun off v hm k hk => ht.world.2.1 _ (hsav off v hm k hk)
    rw [← hmr.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    exact ht.world.2.1 _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))
  · -- no outgoing area: the canonical body-entry world is the actual activation's
    obtain ⟨hib0, hsz0⟩ := hib.resolve_right hN
    have hFh : Fh = F := funext fun a => propext ⟨fun h => h.1, fun h => ⟨h, fun ⟨o1, o2⟩ => by
      omega, fun ⟨o1, o2⟩ => by omega⟩⟩
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ := by
      rw [hFh]; exact L.bodyEntryW_compat hL hh himgF ht
    have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
    exact hallG G (Arm.r .PC t + 4) (enterAt (L.A h) t) (hME t w₀ hst herrt ht.img hbw)

/-- **The callee's states of a returning call of a function of `P`** (`progOsCore`'s premises):
from `ThmG` one level down. -/
theorem progGoodCore (hL : L.Ok) {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w w' : Arm.ArmState} {outs : List CV}
    (hG : ∀ a, G a → t.mem a = s0.mem a) (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progX κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    L.RunGoodL (M - 1) h (enterAt (L.A h) t) := by
  have hpf := func?_of_mem hL.names hh
  have hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize) ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize
      · exact .inl ⟨h0, h1⟩
      · exact .inr ⟨g, hg, h, hcallee, .inr h1⟩
    · exact .inr ⟨g, hg, h, hcallee, .inl h0⟩
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  unfold progX at hx
  have hcond : L.Cond κ M F h uses w ∧
      Arm.r .ERR (L.pcall M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, rvals, cm', hmr, hargs, hsav, hpl, hinit,
    hrun⟩, -⟩ := hcond
  have hcOk : L.CallerOk F h uses w t := by
    refine ⟨hsw, fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_,
      hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : uses[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [← huses, hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  exact L.progCallG hL hM (ihG hM) hpf ⟨g, hg, hcallee⟩ hib himgF herrw halw hroom hdead hmr
    hargs hsav hpl hinit hrun t hcOk

/-- **The callee of a `blr` at a call state is one `g` may enter through the call's register**
(`BlrTo`): the callee contract's premise (`RL.CallPre`) is a call through `L.X`, which enters a
function of `P` only when `g` may enter it (`IndTo`), and pins a call through the GOT to its
symbol (`gotGuard`). -/
theorem blrTo_of_pre (hL : L.Ok) {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState} {h : Clif.Function}
    (hpre : (L.actRL κ M g F G s).CallPre u) (hprog : u.program = (L.A g).fb.program (L.A g).base)
    {xr : Reg} (hx0 : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some (.blr xr))
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) :
    ∃ info tv, (L.A g).vcp.CallSite info ∧ info.dest = .reg (.vreg tv .int) ∧ L.BlrTo g tv h := by
  obtain ⟨ctx, i, ctl, ⟨info, hsite, hi⟩, -, -, hGk, c, wh, ops, regs, i', w, outs, w', hops, hst,
    hasg, hP, -, -, -, hsem⟩ := hpre
  have hsite : (L.A g).vcp.CallSite info := hsite
  have hGk : ∀ a, G a → u.mem a = s.mem a := hGk
  have hFe : (L.actRL κ M g F G s).F = F := he.hF
  have hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' := hP
  have hsem : csemV (GotV (L.A g).vcp) F ctx (L.X κ M g F) i (useVals ops regs u) w =
      some (outs, w', ctl) := hFe ▸ hsem
  -- the plain call of the instruction
  obtain ⟨ic, hasgC, hPC, hopsC, hst', hx, hguard⟩ : ∃ ic,
      (MInst.call info).assign regs = .ok (.call ic) ∧
      CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) (.call ic) ∧
      (MInst.call info).operands = .ok ops ∧
      (∃ clob, c.checkStatic wh ops (regs.map .reg) clob = .ok ()) ∧
      (∃ o w2, (L.X κ M g F).call (match info.dest with | .sym n => some n | .reg _ => none)
        (useVals ops regs u) w = some (o, w2)) ∧
      gotGuard (GotV (L.A g).vcp) (L.X κ M g F) info (useVals ops regs u) := by
    rcases hi with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, hx, -⟩ := h0
      exact ⟨ic, hasg, hP, hops, ⟨_, hst⟩, ⟨o, w2, hx⟩, csemV_guard hsem⟩
    · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, ⟨hx, -⟩, -⟩ := h0
      exact ⟨ic, hasg', callAt_tryCall_call hP,
        by rw [← operands_tryCall_call info ti]; exact hops, ⟨_, hst⟩, ⟨o, w2, hx⟩,
        csemV_guard_try hsem⟩
  obtain ⟨j, x, tt, hj, hx', hpc⟩ := hPC
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hins : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x := by
    rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hprog hj
  obtain ⟨o, w2, hx⟩ := hx
  obtain ⟨clob, hst'⟩ := hst'
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d0, us0, ds0⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', hic⟩ := assign_call_sym hasgC
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    rw [hins] at hx0; cases hx0
  | reg r =>
    have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
    rw [operands_call_reg] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasgC
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u (fun a ha => (hGk a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      rw [htgt] at hb; exact hb
    have hx2 : (L.X κ M g F).call none (regVal u (.x n0) :: Lu.map (fun q => regVal u q.2)) w =
        some (o, w2) := by
      rw [← call_useVals_reg hregs0]; exact hx
    rw [L.X_ind hs] at hx2
    split at hx2
    · rename_i hdecl
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      exact ⟨_, tv, hsite, rfl, hdecl.1, hgot⟩
    · cases hx2

/-- **The crux: the callee's states at a call state.** At a state `u` of the activation of `g`
at depth `M` where the callee contract's premise holds (`RL.CallPre`, which `RL.GoodX.call` gives
at a `bl`/`blr` line) and the machine calls `h` (`CallsAtL`), every state of `h`'s run entered
from `u` whose step ends without error has the per-state facts: the premise is the antecedent of
`progOs`/`progOsReg` (`calleeOk`), whose linked call of `h` is the callee activation of
`progCall`, whose states `ThmG` one level down covers. -/
theorem callGood (hL : L.Ok) {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState} {h : Clif.Function}
    (hpre : (L.actRL κ M g F G s).CallPre u) (hprog : u.program = (L.A g).fb.program (L.A g).base)
    (hcall : L.CallsAtL g u h) : L.RunGoodL (M - 1) h (enterAt (L.A h) u) := by
  obtain ⟨ctx, i, ctl, ⟨info, hsite, hi⟩, -, -, hGk, c, wh, ops, regs, i', w, outs, w', hops, hst,
    hasg, hP, hsw, -, -, hsem⟩ := hpre
  have hsite : (L.A g).vcp.CallSite info := hsite
  have hGk : ∀ a, G a → u.mem a = s.mem a := hGk
  have hFe : (L.actRL κ M g F G s).F = F := he.hF
  have hsw : SameWorld F u w := hFe ▸ hsw
  have hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' := hP
  have hsem : csemV (GotV (L.A g).vcp) F ctx (L.X κ M g F) i (useVals ops regs u) w =
      some (outs, w', ctl) := hFe ▸ hsem
  -- the plain call of the instruction
  obtain ⟨ic, hasgC, hPC, hopsC, hst', hx, hguard⟩ : ∃ ic,
      (MInst.call info).assign regs = .ok (.call ic) ∧
      CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) (.call ic) ∧
      (MInst.call info).operands = .ok ops ∧
      (∃ clob, c.checkStatic wh ops (regs.map .reg) clob = .ok ()) ∧
      (∃ o w2, (L.X κ M g F).call (match info.dest with | .sym n => some n | .reg _ => none)
        (useVals ops regs u) w = some (o, w2)) ∧
      gotGuard (GotV (L.A g).vcp) (L.X κ M g F) info (useVals ops regs u) := by
    rcases hi with rfl | ⟨ti, rfl⟩
    · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, hx, -⟩ := h0
      exact ⟨ic, hasg, hP, hops, ⟨_, hst⟩, ⟨o, w2, hx⟩, csemV_guard hsem⟩
    · obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      have h0 := csemV_sub hsem
      simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h0
      obtain ⟨⟨o, w2⟩, ⟨hx, -⟩, -⟩ := h0
      exact ⟨ic, hasg', callAt_tryCall_call hP,
        by rw [← operands_tryCall_call info ti]; exact hops, ⟨_, hst⟩, ⟨o, w2, hx⟩,
        csemV_guard_try hsem⟩
  have hcp := hPC.callPc
  obtain ⟨j, x, tt, hj, hx', hpc⟩ := hPC
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hins : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x := by
    rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hprog hj
  obtain ⟨o, w2, hx⟩ := hx
  obtain ⟨clob, hst'⟩ := hst'
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d0, us0, ds0⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', hic⟩ := assign_call_sym hasgC
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have hpf : L.P.func? n = some h := by
      rcases hcall with ⟨n', hn', hpf'⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hpf'
      · rw [hins] at hr'; cases hr'
    obtain ⟨hh, -⟩ := Clif.Program.func?_some hpf
    have hps : L.ProgSite g ⟨.sym n, us0, ds0⟩ h := ⟨hsite, n, rfl, hpf⟩
    obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg _ h hps
    cases hinfo
    rw [operands_call_sym] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    have hx2 : L.progX κ M F h (Lu.map (fun q => regVal u q.2)) w = some (o, w2) := by
      rw [← L.X_prog (κ := κ) (M := M) (g := g) hpf, ← call_useVals hregs]; exact hx
    exact L.progGoodCore hL ihG hg hh (.inl ⟨_, hps⟩) he.imgF he.imgG he.imgS hLu hGk
      (hL.raCall g hg _ h hps _ hcp) hsw hx2
  | reg r =>
    have hreg : ∀ n, info.dest ≠ .sym n := fun n => by rw [hd]; simp
    obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
    rw [operands_call_reg] at hopsC
    cases hopsC
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst'
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasgC
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    cases hic
    simp only [MInst.callInsn?, Option.some.injEq] at hx'
    subst hx'
    have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg u (fun a ha => (hGk a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
      rcases hcall with ⟨n', hn', -⟩ | ⟨-, hb⟩
      · rw [hins] at hn'; cases hn'
      · rw [htgt] at hb; exact hb
    have hx2 : (L.X κ M g F).call none (regVal u (.x n0) :: Lu.map (fun q => regVal u q.2)) w =
        some (o, w2) := by
      rw [← call_useVals_reg hregs0]; exact hx
    rw [L.X_ind hs] at hx2
    split at hx2
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_reg tv Lu Ld) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_reg hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      obtain ⟨hLu, -⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      exact L.progGoodCore hL ihG hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) he.imgF he.imgG he.imgS hLu
        hGk (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hcp) hsw hx2
    · cases hx2

/-! ## The states of an activation's run -/

/-- **The states of the activation of `g` at depth `M` entered in `s`** from its trace (the
register-level `GoodX` of every state before `n`), when every state before its return whose step
ends without error is before `n`: its own states from the trace, the nested ones from the call
states (`callGood`). -/
theorem runGood_of_trace (hL : L.Ok) {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : L.MachEntry κ M g F G ra s w₀) {n : Nat}
    (hgood : ∀ i < n, actGoodX (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s (L.X κ M g F) (L.hooks M) (κ M g) G (GotV (L.A g).vcp)
      (runX (L.mach M g) i s))
    (hbound : ∀ k, (∀ j ≤ k, ¬ RetL (L.A g) s (runX (L.mach M g) j s)) →
      Arm.r .ERR (runX (L.mach M g) (k + 1) s) = .None → k < n) :
    L.RunGoodL M g s := by
  intro M' g' c' t hR herrt
  cases hR with
  | act hno =>
    rename_i k
    have hG : (L.actRL κ M g F G s).GoodX (runX (L.mach M g) k s) :=
      hgood k (hbound k hno (by rw [runX_add]; exact herrt))
    refine ⟨L.X κ M g F, κ M g, G, GotV (L.A g).vcp, rfl, hG, he.imgG, he.imgS, ?_⟩
    intro xr h hx hb
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hsz : ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
      rw [layout_sum hc.layout]; have := hL.fits g hg; omega
    have hx' : insnAt (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) k s)) = some x := by
      rw [hpc]; exact insnAt_line hsz hj'
    rw [hx'] at hx; cases hx
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach M g) k s))
        (Arm.r .PC (runX (L.mach M g) k s)) = some (.blr xr) := by
      rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hG.prog hj'
    exact L.blrTo_of_pre hL hg he (hG.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨xr, rfl⟩)) hG.prog hins hb
  | nest hno hcall herr1 hR' =>
    rename_i M0 k h
    have hG : (L.actRL κ (M0 + 1) g F G s).GoodX (runX (L.mach (M0 + 1) g) k s) :=
      hgood k (hbound k hno herr1)
    obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := hG.line
    have hj' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := hj
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have hins : insnAt (L.A g).fa (progBase (runX (L.mach (M0 + 1) g) k s))
        (Arm.r .PC (runX (L.mach (M0 + 1) g) k s)) = some x := by
      rw [hpc]; exact insnAt_ofLine hc.layout hlm (by have := hL.fits g hg; omega) hG.prog hj'
    have hpre : (L.actRL κ (M0 + 1) g F G s).CallPre (runX (L.mach (M0 + 1) g) k s) := by
      rcases hcall with ⟨n', hn', -⟩ | ⟨⟨r', hr'⟩, -⟩
      · rw [hins] at hn'; cases hn'; exact hG.call _ ⟨j, tt, hj, hpc⟩ (.inl ⟨n', rfl⟩)
      · rw [hins] at hr'; cases hr'; exact hG.call _ ⟨j, tt, hj, hpc⟩ (.inr ⟨r', rfl⟩)
    exact L.callGood hL ihG hg he hpre hG.prog hcall _ _ _ _ hR' herrt

/-- A returning activation (`ActRet`) has returned in the sense of `RetL`. -/
theorem retL_of_actRet {g : Clif.Function} {ra : BitVec 64} {s t : Arm.ArmState}
    {F G : BitVec 64 → Prop} {us : List (Reg × Reg)} {outs : List CV} {wf : Arm.ArmState}
    (habi : AbiCall (L.A g).fb (L.A g).base ra s) (hret : ActRet ra F G us outs wf s t) :
    RetL (L.A g) s t :=
  ⟨hret.ret.pc.trans habi.lr.symm, hret.ret.err, hret.prog.trans habi.program, hret.ret.sp⟩

/-- **The per-state part of the induction step.** -/
theorem thmG_of (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1))
    (ihG : 0 < M → L.ThmG κ (M - 1)) : L.ThmG κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' hWE hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  have hrun' : Clif.runLoop (L.envOf M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOf hL hg fuel cs hJ]; exact hrun
  have h := backend_correct_world_niX ((hL.subset g hg).retarget (Clif.Program.bare_func? L.P)) hc
    (X := L.X κ M g F) (syms := L.syms)
    (env := L.envOf M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    (L.xCallsOk hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (L.xCallsIndOk hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (trapsExplicit_of_returned hrun') fuel
  obtain ⟨_us, _outs, _wf, -, -, -, -, -, hall, hni⟩ := h rvals cm' hrun'
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G (L.X κ M g F)
        (L.hooks M) (L.A g).base ra s w₀' := fun G ra s w₀' hME =>
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk hL hκ ih hg hME,
      fun _ => L.calleeTryOk hL hκ ih hg hME,
      fun ht => L.tlsOk_hooks (hL.baseTls g hg (hasTls_of_vcode hc ht) F (κ M g)), hME.body⟩
  refine ⟨fun G ra s hME => ?_, fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
  · obtain ⟨n, hret, -, hgood⟩ := hall (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀ hME)
    exact L.runGood_of_trace hL ihG hg hME hgood fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet hME.abi hret)
  · obtain ⟨n, hret, -, hgood⟩ := hni (L.xni hL hN ih hg hWE.img (spv w₀)) (L.xTls hL hN) D w₀'
      hrel' hsw hreg hstk (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀' hME)
    exact L.runGood_of_trace hL ihG hg hME hgood fun k hno _ =>
      Nat.lt_of_not_le fun hle => hno n hle (L.retL_of_actRet hME.abi hret)

/-- **The per-state part of the linking statement at every depth.** -/
theorem thmG (hL : L.Ok) (hκ : L.Budget κ) : ∀ M, L.ThmG κ M
  | 0 => L.thmG_of hL hκ (fun h => absurd h (Nat.lt_irrefl 0)) fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thmG_of hL hκ (fun _ => L.thm hL hκ M) fun _ => thmG hL hκ M

/-- **The induction step of the linking statement with the per-state facts.** -/
theorem thmX_of (hL : L.Ok) (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmX κ (M - 1)) :
    L.ThmX κ M :=
  ⟨L.thm_of hL hκ fun h => (ih h).1, L.thmG_of hL hκ (fun h => (ih h).1) fun h => (ih h).2⟩

/-- **The linking statement with the per-state facts at every depth.** -/
theorem thmX (hL : L.Ok) (hκ : L.Budget κ) : ∀ M, L.ThmX κ M
  | 0 => L.thmX_of hL hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thmX_of hL hκ fun _ => thmX hL hκ M

end LinkSys

/-- **`backend_correct_program_budgetX`**: `backend_correct_program_budget` with the run's per-state facts for a returning or
trapping outcome. -/
theorem backend_correct_program_budgetX (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  refine ⟨backend_correct_program_budget L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
    hrel hpl htr, fun hout => ?_⟩
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  have hst := hres
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs fun off v hm k hk hk' => ?_
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB]; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB, hd]
      have := hent.spAligned
      have := L.frameSize_mod hL hf
      omega
  -- the machine side
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  -- the whole-program run is a run of the program without functions
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  have hlink := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (hL.subset f hf).externCalls (hL.subset f hf).tryExterns (E := L.envR M f)
    rfl rfl (fun _ hn => L.envR_of (.inl hn))
    (L.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
  cases ho : Clif.runLoop L.base L.P (M + 1) cs with
  | stuck m => rw [ho] at hout; simp at hout
  | outOfFuel => rw [ho] at hout; simp at hout
  | returned vals cm =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    rw [ho] at hm
    exact (L.thmG hL hκ M f hf L.F args cs w₀ m vals cm hWE hm).1 L.Img ra s hME
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    rw [ho] at hm
    have ih : 0 < M → L.Thm κ (M - 1) := fun _ => L.thm hL hκ (M - 1)
    have hJ : L.ActInv f (spv w₀) cs := ⟨hIf, hcs.callers, hpl⟩
    have hm' : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .trapped c := by
      rw [L.runLoop_envOf hL hf m cs hJ]; exact hm
    have h := backend_correct_worldX ((hL.subset f hf).retarget (Clif.Program.bare_func? L.P)) hc
      (X := L.X κ M f L.F) (syms := L.syms)
      (env := L.envOf M f (spv w₀)) (K := κ M f) (F := L.F) (c := spv w₀) (hL.covered f hf)
      (L.xCallsOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (L.xCallsIndOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
      (L.trapsExplicit_envOf hL hf hJ htr) m
    obtain ⟨n, -, hgood, hstuck⟩ := h.2 c hm' (L.hooks M) L.Img (L.A f).base ra s
      ⟨hME.abi, hME.stack, hME.gfree, hME.hF,
        L.calleeOk hL hκ ih hf hME,
        fun _ => L.calleeTryOk hL hκ ih hf hME,
        fun ht => L.tlsOk_hooks (hL.baseTls f hf (hasTls_of_vcode hc ht) L.F (κ M f)), hME.body⟩
    refine L.runGood_of_trace hL (fun _ => L.thmG hL hκ (M - 1)) hf hME hgood fun k _ hk => ?_
    refine Nat.lt_of_not_le fun hle => hstuck (k - n) ?_
    rw [show n + (k - n) + 1 = k + 1 by omega]
    exact hk

end E2E
