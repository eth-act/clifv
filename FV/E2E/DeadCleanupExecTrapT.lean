import FV.E2E.DeadCleanupExecTrap
import FV.E2E.LinkTrapCallT

/-! # Callee traps on the executable machine, `try_call`s included (S9e, #408)

`FV/E2E/DeadCleanupExecTrap.lean` without "no `try_call` terminator": the executable trap
theorems from the linked-program theorems with `try_call`s (`backend_correct_program_trapT_budget`,
`_peak`) under the run premise `TrapsDT`, with the same observable `TrapAtE` (`exec_trap_of_model`).

* `trapsOkT_of`: `LinkSys.TrapsOkT` from the checker and the lowering's unwinding validator;
* **`binary_correct_exec_trapT`**, **`binary_correct_exec_trapT_peak`**.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

section Binary

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The run premise `TrapsDT` does not depend on the exterior `F`. -/
theorem trapsDT_F (c : Nat → Clif.State → Clif.Outcome) (F F' : BitVec 64 → Prop) :
    ∀ M, ((LinkSys.ofInputCleanup I B F).withCrun c).TrapsDT M =
      ((LinkSys.ofInputCleanup I B F').withCrun c).TrapsDT M
  | 0 => rfl
  | M + 1 => by
    show ((LinkSys.ofInputCleanup I B F).withCrun c).TrapsAtT (M + 1)
        (((LinkSys.ofInputCleanup I B F).withCrun c).TrapsDT M) =
      ((LinkSys.ofInputCleanup I B F').withCrun c).TrapsAtT (M + 1)
        (((LinkSys.ofInputCleanup I B F').withCrun c).TrapsDT M)
    rw [trapsDT_F c F F' M]
    rfl

theorem std_trapsDT_F {F F' : BitVec 64 → Prop} {M : Nat} {g : Clif.Function} {cs : Clif.State}
    (h : (LinkSys.ofInputCleanup I B F).std.TrapsDT M g cs) :
    (LinkSys.ofInputCleanup I B F').std.TrapsDT M g cs := by
  have e := trapsDT_F (I := I) (B := B) (fun M => Clif.runLoop (sys I B).base (sys I B).P M) F F' M
  exact e ▸ h

theorem peak_trapsDT_F {F F' : BitVec 64 → Prop} {Fu M : Nat} {g : Clif.Function}
    {cs : Clif.State} (h : ((LinkSys.ofInputCleanup I B F).peak Fu).TrapsDT M g cs) :
    ((LinkSys.ofInputCleanup I B F').peak Fu).TrapsDT M g cs := by
  have e := trapsDT_F (I := I) (B := B) (fun M => Clif.runD (sys I B).base (sys I B).P Fu M) F F' M
  exact e ▸ h

/-- The per-function facts of the trap theorem with `try_call`s from the checker (`okBCleanup`)
and the lowering's unwinding validator. -/
theorem trapsOkT_of {F : BitVec 64 → Prop} (hI : okBCleanup I = true)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true) :
    (LinkSys.ofInputCleanup I B F).TrapsOkT where
  cleanup g hg := by
    have hf := factsCleanup hI hg
    exact ⟨hf.pipe.1, hf.lowerOk, hf.pipe.2.1, hf.prepOk, hf.check, hf.pipe.2.2.1,
      hf.pipe.2.2.2.1, hf.pipe.2.2.2.2.1⟩
  lowerU := hU

/-- **The binary theorem about the executable's own words with callee traps** (entries without
a reachable call cycle): under the premises of `binary_correct_exec_proven` (no GOT slot in the
executable), the lowering's unwinding validator and the outside code's trap contract (`BaseTrapsOk`), a
whole-program CLIF run that traps with `tc` under the run premise `TrapsDT` (no memory-access trap;
traps of the callees of calls and `try_call`s allowed) reaches, on the executable machine from
`r`, a state at a trap with `tc` (`TrapAtE`). -/
theorem binary_correct_exec_trapT {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true)
    (hBT : (sys I B).BaseTrapsOk) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs) (htr : (sys I B).std.TrapsDT M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped tc) :
    ∃ k, TrapAtE I B tc (runX (step I B file) k r) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  have hfm := (Clif.Program.func?_some hf).1
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  unfold DeadCleanupStackBound.goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hκ := DeadCleanupStackBound.budget_of hI B (worldF I f (DeadCleanupStackBound.bud I f) r)
  have hκf : ∀ M, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).hybrid
      (DeadCleanupStackBound.budO I) (DeadCleanupStackBound.budMax I) M f =
      DeadCleanupStackBound.bud I f := fun M => by simp [LinkSys.hybrid, hb, hbud]
  have hT := backend_correct_program_trapT_budget _ hL0 (trapsOkT_of hI hU) (baseTrapsOk_F hBT)
    hκ hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf M]; exact hκ.2 M f hfm⟩) (by rw [hκf]; rfl)
    (by rw [hκf]; exact hgfree) himg hbe hargs
    hr.entry hsav hrel hpl (std_trapsDT_F htr) hrun
  exact exec_trap_of_model hI hcm hbin hnogot hB hH hf hX ho hr hT

/-- **`binary_correct_exec_trapT` for the run's peak call depth** (any program, recursive ones
included): the stack `frameDrop + (D * d + pbMax I)` of the run's call depth `d` (`Clif.DepthLe`;
#581: with the stack probes of the deepest activation), the run
premise `TrapsDT` of the callees running with fuel `F` and at most `d - 1` callers of their own
(`LinkSys.peak`). -/
theorem binary_correct_exec_trapT_peak {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true)
    (hBT : (sys I B).BaseTrapsOk) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f) (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r
      args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : ((sys I B).peak F).TrapsDT d f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (F + 1) cs = .trapped tc) :
    ∃ k, TrapAtE I B tc (runX (step I B file) k r) := by
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (I.D * d + pbMax I) r)) := baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hT := backend_correct_program_trapT_peak _ hL0 (trapsOkT_of hI hU) (baseTrapsOk_F hBT)
    (LinkSys.budget_K _ hL0) hfm F d hent ⟨hres, (LinkSys.budget_K _ hL0).2 d f hfm⟩ rfl hgfree himg
    hbe hargs hr.entry hsav hrel hpl
    hd (peak_trapsDT_F htr) hrun
  exact exec_trap_of_model hI hcm hbin hnogot hB hH hf hX ho hr hT

end Binary

end E2E.DeadCleanupExecBytes
