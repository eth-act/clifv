import FV.E2E.LinkTrapCallInd
import FV.E2E.WorldTrapStopT

/-! # Callee traps in the linked program, `try_call`s included (S9e, #408)

`FV/E2E/LinkTrapCallInd.lean` without its premise "no `try_call` terminator"
(`LinkSys.TrapsOk.noTry`): the induction applies the per-function world theorem with `try_call`s
(`backend_correct_world_cleanup_trapstopT`) and the run premise allows traps of the callees of
`try_call`s.

* `LinkSys.TrapsOkT`: `TrapsOk` without `noTry` (`TrapsOk.toT`);
* `LinkSys.TrapsAtT`, `LinkSys.TrapsDT`: `TrapsAt`/`TrapsD` with `TrapsExplicitCT` (no
  memory-access trap; a trap of the callee of a `call`, `call_indirect`, `try_call` or
  `try_call_indirect` allowed);
* `LinkSys.thmTT`: the induction (`ThmTG L.TrapsDT`), the callee-trap states at call sites of
  either kind going through `trapIn_callTrapG`;
* **`E2E.backend_correct_program_trapT_budget`**, `backend_correct_program_trapT`,
  `backend_correct_program_trapT_peak`: the whole-program trap theorems with the same observable
  `TrapIn` (its call sites, `CallSite`, are of either kind).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The program's functions as the trap theorem with `try_call`s needs them** (all decided by
the compiler): compiled by the shipped dead-cleanup pipeline, passing the lowering's unwinding
validator. -/
structure TrapsOkT : Prop where
  cleanup : ∀ g ∈ L.P.funcs, CompiledCleanup g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb
  lowerU : ∀ g ∈ L.P.funcs, lowerCheckU g (L.A g).vc = true

theorem TrapsOk.toT {L : LinkSys} (h : L.TrapsOk) : L.TrapsOkT := ⟨h.cleanup, h.lowerU⟩

/-- **The run premise of an activation of `g` at depth `M` with `try_call` callee traps**
(`TrapsAt` with `TrapsExplicitCT`), given the premise `D` of the program callees' activations. -/
def TrapsAtT (M : Nat) (D : Clif.Function → Clif.State → Prop) (g : Clif.Function)
    (cs : Clif.State) : Prop :=
  TrapsExplicitCT (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs ∧
  ∀ fuel tc, Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped tc →
    Clif.runLoop (cutEnv (L.envR M g) (L.covQ D)) L.P.bare fuel cs = .trapped tc

end LinkSys

/-- **The run premise of the linked program with callee traps, `try_call`s included**
(`LinkSys.TrapsD` with `TrapsExplicitCT`), by depth. -/
def LinkSys.TrapsDT (L : LinkSys) : Nat → Clif.Function → Clif.State → Prop
  | 0 => L.TrapsAtT 0 fun _ _ => False
  | M + 1 => L.TrapsAtT (M + 1) (LinkSys.TrapsDT L M)

/-- The premise of the program callees' activations of an activation at depth `M`. -/
def LinkSys.TrapsDTn (L : LinkSys) : Nat → Clif.Function → Clif.State → Prop
  | 0 => fun _ _ => False
  | M + 1 => L.TrapsDT M

theorem LinkSys.trapsDT_eq (L : LinkSys) (M : Nat) (g : Clif.Function) (cs : Clif.State) :
    L.TrapsDT M g cs = L.TrapsAtT M (L.TrapsDTn M) g cs := by
  cases M <;> rfl

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The run premise of `P.bare` under `linkEnvR` is the one under `envOf` with some extern
outcomes stuck** (`trapsExplicitC_cut` for `TrapsExplicitCT`). -/
theorem trapsExplicitCT_cut (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {Q : String → List Clif.Val → Clif.Mem → Prop}
    {cs : Clif.State} (hJ : L.ActInv g c cs)
    (h : TrapsExplicitCT (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicitCT (cutEnv (L.envOf M g c) Q) L.P.bare cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reach_cut hL hg hr hJ
    exact h.stmt s c st rest hr' (L.step_cut_link hL hg hJs hs (fun _ h => nomatch h)) hb
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_cut hL hg hr hJ).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_cut hL hg hr hJ).1 hb ht hB

theorem trapsDTn_succ {M : Nat} {h : Clif.Function} {cs : Clif.State} (hD : L.TrapsDTn M h cs) :
    ∃ M', M = M' + 1 ∧ L.TrapsDT M' h cs := by
  cases M with
  | zero => exact hD.elim
  | succ M' => exact ⟨M', rfl, hD⟩

/-- **The induction step with `try_call`s**: the trap statement at depth `M` from the one at
depth `M - 1` (and the linking statement `LinkSys.thm` for the returning callees). -/
theorem thmTT_of (hL : L.Ok) [hR : L.CrunOk] (hT : L.TrapsOkT) (hB : L.BaseTrapsOk)
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmTG L.TrapsDT κ (M - 1)) :
    L.ThmTG L.TrapsDT κ M := by
  intro g hg F vals cs w₀ fuel tc hWE hTD hrun G ra s hME
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  rw [L.trapsDT_eq] at hTD
  obtain ⟨htrC, hcut⟩ := hTD
  have hrunE : Clif.runLoop (cutEnv (L.envOf M g (spv w₀)) (L.covQ (L.TrapsDTn M))) L.P.bare fuel
      cs = .trapped tc := by
    rw [L.runLoop_cut hL hg fuel cs hJ]; exact hcut fuel tc hrun
  have htrE := L.trapsExplicitCT_cut hL hg (Q := L.covQ (L.TrapsDTn M)) hJ htrC
  have ihR : 0 < M → L.Thm κ (M - 1) := fun _ => L.thm hL hκ (M - 1)
  have hAE : ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.X κ M g F) (L.hooks M) (L.A g).base ra s w₀ :=
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk hL hκ ihR hg hME,
      fun _ => L.calleeTryOk hL hκ ihR hg hME,
      fun ht => L.tlsOk_hooks (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)), hME.body⟩
  have hDn : ∀ {h : Clif.Function} {cs : Clif.State}, L.TrapsDTn M h cs → 0 < M →
      L.TrapsDT (M - 1) h cs := fun hD _ => by
    obtain ⟨M', rfl, hD'⟩ := L.trapsDTn_succ hD
    exact hD'
  obtain ⟨n, htrace, hsp, hprog, hcase⟩ := backend_correct_world_cleanup_trapstopT
    (hL.subset g hg) (hT.cleanup g hg) (hT.lowerU g hg) rfl
    (X := L.X κ M g F) (syms := L.syms) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    (xCallsOk_cut (L.xCallsOk hL hκ ihR hg hWE.img hWE.room hWE.dead hWE.align))
    (xCallsIndOk_cut (L.xCallsIndOk hL hκ ihR hg hWE.img hWE.room hWE.dead hWE.align))
    (L.xTrapsOkG hL hB hκ hDn ih hg hWE.img)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args htrE hrunE
    (L.hooks M) G (L.A g).base ra s hAE
  have hroom : frameDrop (L.A g).af ≤ (spv s).toNat := by
    rw [L.frameDrop_eq hL hg]; have := hME.stack.1; omega
  have htr : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n :=
    by have := postTrace_of_actGoodX htrace; exact this
  have hgoodOf : (∀ m, Arm.r .ERR (runX (L.mach M g) (n + m + 1) s) ≠ .None) →
      L.RunGoodL M g s := fun hh =>
    L.runGood_of_trace hL hκ (fun _ => L.thmG hL hκ (M - 1)) hg hME (by exact htrace)
      fun k _ he => Nat.lt_of_not_le fun hle => hh (k - n) (by
        rw [show n + (k - n) + 1 = k + 1 by omega]; exact he)
  rcases hcase with ⟨hat, hhalt⟩ | hct
  · exact .site ⟨hroom, htr, hat.err, hprog, hsp, hhalt, hgoodOf hhalt⟩ hat
  · have herr : Arm.r .ERR (runX (L.mach M g) n s) = .None := by
      obtain ⟨_, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := hct
      exact he
    have hhalt : Arm.r .ERR (L.mach M g (runX (L.mach M g) n s)) ≠ .None →
        ∀ m, Arm.r .ERR (runX (L.mach M g) (n + m + 1) s) ≠ .None := fun he m => by
      rw [show n + m + 1 = n + (m + 1) by omega, runX_add]
      exact L.runX_mach_err hB M g m _ he
    exact L.trapIn_callTrapG (D := L.TrapsDT) hL hB hκ (L.trapsDTn_succ) ih hg hWE hME
      (fun he => ⟨hroom, htr, herr, hprog, hsp, hhalt he, hgoodOf (hhalt he)⟩) hprog hct

/-- **The trap statement with `try_call`s at every depth.** -/
theorem thmTT (hL : L.Ok) [L.CrunOk] (hT : L.TrapsOkT) (hB : L.BaseTrapsOk) (hκ : L.Budget κ) :
    ∀ M, L.ThmTG L.TrapsDT κ M
  | 0 => L.thmTT_of hL hT hB hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thmTT_of hL hT hB hκ fun _ => thmTT hL hT hB hκ M

/-- The premises of the trap theorem do not read the callee runs. -/
theorem TrapsOkT.withCrun {L : LinkSys} (h : L.TrapsOkT) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).TrapsOkT :=
  ⟨h.cleanup, h.lowerU⟩

end LinkSys

/-! ## The whole-program theorem with callee traps, `try_call`s included -/

/-- **The whole-program trap theorem with `try_call`s for any callee runs** (`LinkSys.CrunOk`;
`backend_correct_program_trap_core` under `TrapsOkT` and `TrapsDT`). -/
theorem backend_correct_program_trapT_core (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    (hT : L.TrapsOkT) (hB : L.BaseTrapsOk)
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
    (htr : L.TrapsDT M f cs) {tc : Clif.TrapCode} {m : Nat}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare m cs = .trapped tc) :
    L.TrapIn M f s tc := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB', hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs (fun off v hm k hk hk' => ?_) hres
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB']; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB'] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB', hd]
      have := hent.spAligned
      have := L.frameSize_mod hL hf
      omega
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  exact L.thmTT hL hT hB hκ M f hf L.F args cs w₀ m tc hWE htr hrun L.Img ra s hME

/-- **The whole-program theorem with callee traps, `try_call`s included, per-function stack
budget `κ`** (`backend_correct_program_trap_budget` without "no `try_call` terminator", under the
run premise `TrapsDT`): the linked machine of depth `M` has the trap observable `TrapIn`: it stops
at a trap site of `f` with `c`, at a call (of either kind) of `f` whose callee outside `P` traps
with `c`, or at a call of a function of `P` whose own activation has the observable one level
down. -/
theorem backend_correct_program_trapT_budget (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOkT)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
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
    (htr : L.std.TrapsDT M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc := by
  haveI := L.crunOk_std hL
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trapT_core L.std (hL.withCrun _)
    (hT.withCrun _) (hB.withCrun _) hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl
    htr hm)

/-- **The whole-program theorem with callee traps, `try_call`s included** (the stack budget
`L.K M`). -/
theorem backend_correct_program_trapT (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOkT)
    (hB : L.BaseTrapsOk) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : L.std.TrapsDT M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc :=
  backend_correct_program_trapT_budget L hL hT hB (κ := fun M _ => L.K M) (L.budget_K hL) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- **The whole-program theorem with callee traps, `try_call`s included, for the run's peak call
depth** (`backend_correct_program_trap_peak` under `TrapsOkT` and `TrapsDT`). -/
theorem backend_correct_program_trapT_peak (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOkT)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLe L.base L.P d cs)
    (htr : (L.peak F).TrapsDT d f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .trapped tc) :
    L.TrapIn d f s tc := by
  haveI := L.crunOk_peak hL F
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trapT_core (L.peak F) (hL.withCrun _)
    (hT.withCrun _) (hB.withCrun _) hκ hf d hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl
    htr hm)

end E2E
