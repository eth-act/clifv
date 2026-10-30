import FV.Front.Exe
import FV.Link.ExeUnwind
import FV.Front.RenameRunX
import FV.E2E.LegalProgX
import FV.Link.DeadCleanupExeSource

/-!
# The exceptional edges on cg_clif's program, with `i128` (S10f)

`bundle_correct_raw_unwind_src`: `bundle_correct_raw_unwind_ren` without its premise that no
function mentions `i128`. The compiled program is the legalisation of cg_clif's program under the
linked names (`Link.DeadCleanup.prog_eq_legal`); a run with unwinding of cg_clif's function `f`
(in cg_clif's environment `E`, `L.envX = E.ren σ`) is renamed (`Clif.runLoopX_ren`) and matched
by the legalised program's run of `legalize (f.rename σ.fwd)` from the entry with the ABI-split
arguments (`E2E.LegalProgram.legalProg_refinesX`), which the linked machine with unwinding refines
(`Link.DeadCleanup.compileExe_correct_unwind`): a return with the results split by `f`'s return
groups, a trap (of a source run without load/store traps), an exception leaving `f` with the
same exception — each with the memory renamed to the linked names. The machine's fuel and stack
budget `M` are any `M ≥ K`, `K` bounding the legalised run.

Premises beyond `compileExe_correct_unwind`'s (taken about the compiled entry `cs'` of
`legalize (f.rename σ.fwd)`): the source domain (`SrcScopeB`), the linked environment's
contracts where a function mentions `i128` (`HelperOk`/`ExtLegal`/`EnvKeepsBounded` of
`L.envX.toEnv`, `ExtLegalX`/`EnvKeepsAllocsX`/`ExnArityOk` of `L.envX`), no signature known to it
with indirect calls (as `compileExe_correct_source`), the handler-edge check `exnOk` of every
legalised function, the source entry `cs` (`ClifEntry`) with the ABI-split arguments, slots and
memory of `cs'`, and the source run's memories below `2^64`.
-/

namespace Front

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary Link Opt.Legalize128 Backend Backend.Proof
  Backend.Proof.Driver E2E.LegalProgram Opt.Legal Opt.Legal.X

/-! ## Runs with unwinding through a renaming -/

theorem stepX_ren_next {σ : Ren} {E : XEnv} {p : Program} {xs t : XState}
    (h : stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) = .next t) :
    ∃ u, stepX E p xs = .next u ∧ t = u.ren σ := by
  have := stepX_ren σ E p xs
  rw [h] at this
  cases hs : stepX E p xs <;> rw [hs] at this <;>
    simp [XStepResult.ren, XStepResult.erase] at this
  exact ⟨_, rfl, this⟩

theorem stepX_ren_trapped {σ : Ren} {E : XEnv} {p : Program} {xs : XState} {c : TrapCode}
    (h : stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) = .trapped c) : stepX E p xs = .trapped c := by
  have := stepX_ren σ E p xs
  rw [h] at this
  cases hs : stepX E p xs <;> rw [hs] at this <;>
    simp [XStepResult.ren, XStepResult.erase] at this
  rw [this]

theorem reachesX_ren {σ : Ren} {E : XEnv} {p : Program} {xs t : XState}
    (h : ReachesX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) t) :
    ∃ u, ReachesX E p xs u ∧ t = u.ren σ := by
  generalize hx : xs.ren σ = x at h
  induction h generalizing xs with
  | refl => exact ⟨xs, .refl _, hx.symm⟩
  | next hst _ ih =>
    subst hx
    obtain ⟨u1, hu1, rfl⟩ := stepX_ren_next hst
    obtain ⟨u2, h2, rfl⟩ := ih rfl
    exact ⟨u2, .next hu1 h2, rfl⟩

/-- No load/store trap, transported through a renaming. -/
theorem memTrapFreeX_ren {σ : Ren} {E : XEnv} {p : Program} {xs : XState}
    (h : ∀ u, ReachesX E p xs u → MemTrapFree E.toEnv p u.s) :
    ∀ t, ReachesX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) t →
      MemTrapFree (E.ren σ).toEnv (p.rename σ.fwd) t.s := by
  intro t ht c st rest htr hb
  obtain ⟨u, hu, rfl⟩ := reachesX_ren ht
  rw [XEnv.ren_toEnv] at htr
  exact h u hu c st rest (step_ren_trapped htr) (by simpa [XState.ren] using hb)

/-! ## The exceptional edges with `i128` -/

/-- **The linked machine with unwinding at fuel and stack budget `M` refines the outcome `o`** of
the compiled function `g` entered in `cs'`, under `compileExe_correct_unwind`'s premises that
depend on `M` (the stack available, the frame addresses, the image clear of the stack, explicit
traps of the target run). -/
def MachAt (L : LinkSysU) (κ : Nat → Clif.Function → Nat) (g : Clif.Function) (ra : BitVec 64)
    (s : Arm.ArmState) (cs' : State) (M : Nat) (o : XOutcome) : Prop :=
  StackAvail (κ M g) (L.A g).af s →
  L.F = frameWG (κ M g) (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
    (RAFrame.compute (L.A g).vcp (L.A g).rf).size (L.A g).af L.Img s →
  (∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A g).af + κ M g) (spv s) a) →
  TrapsExplicitX (L.stdX.envRX M g) L.P.bare cs' →
  ArmRefinesU (L.A g).fb (L.A g).base ra (L.machU M g) s o

/-- **cg_clif's program's runs with unwinding, matched by the legalised program under the linked
names**: for a program `R` (cg_clif's), its renaming `R.rename σ.fwd` in the source domain with
unwinding under the renamed environment `E.ren σ`, `f` of `R` entered in `cs` on `args` and its
legalisation under the linked names entered in `cs'` on the ABI-split arguments with the same
slots and the renamed memory: a return, a trap (of a run without load/store traps) or an
exception leaving `f` of `R`'s run with unwinding under `E` is one of the legalised program's run
(`legalProg_refinesX` through `Clif.runLoopX_ren`), the memories renamed. -/
theorem raw_legal_unwind {R : Program} {σ : Ren} {E : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxX (R.rename σ.fwd) (E.ren σ) syms) {n : String} {f : Function}
    (hf : R.func? n = some f) {args args' : List Val} {cs cs' : State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry (legalize (f.rename σ.fwd)) args' cs')
    (hexp : ExpRel ((groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hsym : SomeInd (legalProg (R.rename σ.fwd)) → cs'.mem.symbols = syms)
    (hbnd : ∀ u, ReachesX E R cs.toX u → MemBounded u.s.mem) :
    (∀ N rv m2, runLoopX E R N cs.toX = .returned rv m2 →
      ∃ rv', ExpRel ((groups f.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX (E.ren σ) (legalProg (R.rename σ.fwd)) k cs'.toX = .returned rv' (m2.ren σ)) ∧
    (∀ N c, (∀ u, ReachesX E R cs.toX u → MemTrapFree E.toEnv R u.s) →
      runLoopX E R N cs.toX = .trapped c →
      ∃ k, runLoopX (E.ren σ) (legalProg (R.rename σ.fwd)) k cs'.toX = .trapped c) ∧
    (∀ N e m2, runLoopX E R N cs.toX = .unwound e m2 →
      ∃ k, runLoopX (E.ren σ) (legalProg (R.rename σ.fwd)) k cs'.toX = .unwound e (m2.ren σ)) := by
  -- the function
  have hf' : (R.rename σ.fwd).func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [Clif.Program.rename_func?, hf]; rfl
  have hfP := (Clif.Program.func?_some hf').1
  -- the entries
  have hcsR := clifEntry_ren (σ := σ) hcs
  obtain ⟨b0, hb0, h2, h3, h4, h5⟩ := hcsR.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel (f.rename σ.fwd) args args' (cs.ren σ).frame cs'.frame :=
    ⟨hcsR.func, hcs'.func, ⟨b0, hb0, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩,
      by rw [hsl]; rfl, by simpa using hexp⟩
  have hst : (⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩ : State) = cs.ren σ := by
    rw [← hcsR.callers]
  have hmem' : (cs.ren σ).mem = cs'.mem := by rw [hmem]; rfl
  have hst' : (⟨cs'.frame, [], (cs.ren σ).mem⟩ : State) = cs' := by
    rw [hmem', ← hcs'.callers]
  have hX0 : (cs.ren σ).toX = ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ := by
    rw [hst]; simp [State.toX, hcs.callers]
  have hX0' : cs'.toX = ⟨⟨cs'.frame, [], (cs.ren σ).mem⟩, []⟩ := by
    rw [hst']; simp [State.toX, hcs'.callers]
  -- the renamed source run
  have hren : ∀ N o, runLoopX E R N cs.toX = o → (∀ msg, o ≠ .stuck msg) →
      runLoopX (E.ren σ) (R.rename σ.fwd) N ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ =
        o.ren σ := by
    intro N o ho hs
    have := runLoopX_ren σ E R N cs.toX
    rw [← State.toX_ren, hX0, ho] at this
    cases o <;> cases hr : runLoopX (E.ren σ) (R.rename σ.fwd) N
      ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ <;>
      rw [hr] at this <;> simp_all [XOutcome.ren, XOutcome.erase]
  -- good states of the renamed source run
  have hXI : XInv (R.rename σ.fwd) ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ :=
    ⟨⟨hE.lframe hfP, fun _ h => nomatch h⟩, rfl⟩
  have hgood : (∀ u, ReachesX (E.ren σ) (R.rename σ.fwd)
        ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ u →
        MemTrapFree (E.ren σ).toEnv (R.rename σ.fwd) u.s) →
      GoodFromX (E.ren σ) (R.rename σ.fwd) (SomeInd (legalProg (R.rename σ.fwd))) syms
        ⟨⟨(cs.ren σ).frame, [], (cs.ren σ).mem⟩, []⟩ := by
    intro hmtf u hu
    refine ⟨?_, hmtf u hu, fun hI => ?_⟩
    · have hu' := hu
      rw [← hX0, State.toX_ren] at hu'
      obtain ⟨u0, hu0, rfl⟩ := reachesX_ren hu'
      exact Front.memBounded_ren (hbnd u0 hu0)
    · have hS := (hC.indSrcX hI).scope
      rw [hu.symbols hC.ctx.free hS.keep hS.keepU hXI]
      show (cs.ren σ).mem.symbols = syms
      rw [hmem']
      exact hsym hI
  have htgt : ∀ k o, runLoopX (E.ren σ) (legalProg (R.rename σ.fwd)) k
      ⟨⟨cs'.frame, [], (cs.ren σ).mem⟩, []⟩ = o →
      runLoopX (E.ren σ) (legalProg (R.rename σ.fwd)) k cs'.toX = o := fun k o h => by
    rw [hX0']; exact h
  refine ⟨fun N rv m2 hrun => ?_, fun N c hnmt hrun => ?_, fun N e m2 hrun => ?_⟩
  · have hr' := hren N _ hrun (fun _ h => by cases h)
    have hG := hgood (memTrapFree_of_runX hr' (fun _ h => by cases h) (fun h => by cases h))
    obtain ⟨rv', hrel', k, hk⟩ := (legalProg_refinesX hC hfP hE hG N).1 rv (m2.ren σ) hr'
    simp only [Clif.Function.rename_sig] at hrel'
    exact ⟨rv', hrel', k, htgt k _ hk⟩
  · have hr' := hren N _ hrun (fun _ h => by cases h)
    have hmtf := memTrapFreeX_ren (σ := σ) hnmt
    have hG := hgood (fun u hu => by
      have hu' := hu
      rw [← hX0, State.toX_ren] at hu'
      exact hmtf u hu')
    obtain ⟨k, hk⟩ := (legalProg_refinesX hC hfP hE hG N).2.1 c hr'
    exact ⟨k, htgt k _ hk⟩
  · have hr' := hren N _ hrun (fun _ h => by cases h)
    have hG := hgood (memTrapFree_of_runX hr' (fun _ h => by cases h) (fun h => by cases h))
    obtain ⟨k, hk⟩ := (legalProg_refinesX hC hfP hE hG N).2.2 e (m2.ren σ) hr'
    exact ⟨k, htgt k _ hk⟩

/-- **The shipped executable compiler with the unwind tables checked refines cg_clif's
program's runs with unwinding, `i128` included**: for `f` of cg_clif's program `rawLink us sc`
entered in `cs` on `args`, its compiled function `legalize (f.rename σ.fwd)` entered in `cs'` on
the ABI-split arguments `args'`, the linked program with unwinding `L` of the input whose
environment is cg_clif's `E` under the linked names, and the premises of
`compileExe_correct_unwind` for the compiled entry: the unwinder reads every compiled function's
tables from `file`, and a return, a trap (of a source run without load/store traps) or an
exception leaving `f` of cg_clif's run with unwinding is refined by the linked machine with
unwinding at every fuel and stack budget `M ≥ K` — the results split by `f`'s return groups,
the same trap, the same exception, the memories renamed. -/
theorem bundle_correct_raw_unwind_src {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (E : XEnv) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hEX : L.envX = E.ren σ)
    (hbU : Link.DeadCleanup.BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ)
    (hlegal : (∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true) →
      HelperOk L.envX.toEnv ∧ ExtLegal L.envX.toEnv ∧ EnvKeepsBounded L.envX.toEnv ∧
        ExtLegalX L.envX ∧ EnvKeepsAllocsX L.envX ∧ ExnArityOk L.envX)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, L.envX.sigOf n = none)
    (hexn : ∀ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true → ∀ g' cert,
      function128Cert g = .ok (g', cert) → exnOk g g' cert = true)
    {ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Val} {cs cs' : State}
    (hent : AbiEntry (L.A (legalize (f.rename σ.fwd))).fb (L.A (legalize (f.rename σ.fwd))).base
      ra s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A (legalize (f.rename σ.fwd))).af s w₀)
    (hargs : ArgsIn (legalize (f.rename σ.fwd)).sig args' s)
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry (legalize (f.rename σ.fwd)) args' cs')
    (hexp : ExpRel ((groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hsav : StackArgsAvoid L.Img (legalize (f.rename σ.fwd)).sig args' s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A (legalize (f.rename σ.fwd))).af.slotBase,
      (RAFrame.compute (L.A (legalize (f.rename σ.fwd))).vcp
        (L.A (legalize (f.rename σ.fwd))).rf).intBase⟩
      (legalize (f.rename σ.fwd)) cs'.frame.slots cs'.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs'.mem (spv w₀))
    (hbnd : ∀ u, ReachesX E (rawLink us sc) cs.toX u → MemBounded u.s.mem) :
    (∀ g' ∈ L.P.funcs, ∀ pc, (L.A g').base.toNat ≤ pc →
        pc < (L.A g').base.toNat + (L.A g').fb.size →
        EhCheck.unwTables file pc = some ((L.A g').base.toNat, (L.A g').tables)) ∧
    (∀ N rv m2, runLoopX E (rawLink us sc) N cs.toX = .returned rv m2 →
      ∃ rv', ExpRel ((groups f.sig.returns).getD []) rv rv' ∧
        ∃ K, ∀ M, K ≤ M →
          MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.returned rv' (m2.ren σ))) ∧
    (∀ N c, (∀ u, ReachesX E (rawLink us sc) cs.toX u → MemTrapFree E.toEnv (rawLink us sc) u.s) →
      runLoopX E (rawLink us sc) N cs.toX = .trapped c →
      ∃ K, ∀ M, K ≤ M → MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.trapped c)) ∧
    (∀ N e m2, runLoopX E (rawLink us sc) N cs.toX = .unwound e m2 →
      ∃ K, ∀ M, K ≤ M →
        MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.unwound e (m2.ren σ))) := by
  obtain ⟨hL, hU, ht⟩ := Link.DeadCleanup.compileExeU_facts h hB hF hLs hbU
  -- the programs
  have hsrcP : S.inputCleanup.srcProg = (rawLink us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hPL : L.P = prog S.inputCleanup := by rw [hLs]; rfl
  have hpe := Link.DeadCleanup.prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (Link.DeadCleanup.prog_eq S).symm
  have hLP : L.P = legalProg S.inputCleanup.srcProg := hPL.trans hpe
  -- the source domain with unwinding
  have hbase : L.base = L.envX.toEnv := hU.envX.symm
  have hctx : ProgCtx S.inputCleanup.srcProg L.envX.toEnv L.syms :=
    srcCtx hsrc (by rw [hpe', ← hPL]; exact hL.names) (by rw [hpe', ← hPL]; exact hL.free)
      (by rw [hpe', ← hPL]; exact hL.declSig)
      (by rw [hpe', ← hPL, ← hbase]; exact hL.indScope)
      (fun h' => ⟨(hlegal h').1, (hlegal h').2.1, (hlegal h').2.2.1⟩)
      (by rw [hpe']; exact hsig)
  have hC : ProgCtxX S.inputCleanup.srcProg L.envX L.syms :=
    { ctx := hctx
      baseX := fun h' => (hlegal h').2.2.2
      indX := fun ⟨g0, hg0, hnf⟩ => by
        rw [← hLP]
        exact hbU.indScopeX g0 (by rw [hLP]; exact hg0) hnf
      exn := hexn }
  rw [hsrcP, hEX] at hC
  have hraw' := raw_legal_unwind hC hf hcs hcs' hexp hsl hmem
    (fun _ => hrel.1.symbols) hbnd
  rw [← hEX, ← hsrcP, ← hLP] at hraw'
  -- the compiled function
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hsrcP, Clif.Program.rename_func?, hf]; rfl
  have hgP : legalize (f.rename σ.fwd) ∈ L.P.funcs := by
    rw [hLP]; exact List.mem_map_of_mem (Clif.Program.func?_some hf').1
  -- from the legalised run to the machine
  have hmach : ∀ o, (∃ k, runLoopX L.envX L.P k cs'.toX = o) → o ≠ .outOfFuel →
      ∃ K, ∀ M, K ≤ M → MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M o := by
    rintro o ⟨k, hk⟩ hof
    refine ⟨k, fun M hM hres hFw hgfree htr => ?_⟩
    have hr := (Link.DeadCleanup.compileExe_correct_unwind h B F hB hF L hLs hbU hNI hκ hgP M
      hent hres hFw hgfree himg hbe hargs hcs' hsav hrel hpl htr).2
    have hfuel : runLoopX L.envX L.P (M + 1) cs'.toX = o := by
      have := runLoopX_add L.envX L.P k _ (by rw [hk]; exact hof) (M + 1 - k)
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [this, hk]
    rw [hfuel] at hr
    exact hr
  obtain ⟨hR, hT, hU'⟩ := hraw'
  refine ⟨ht, fun N rv m2 hrun => ?_, fun N c hnmt hrun => ?_, fun N e m2 hrun => ?_⟩
  · obtain ⟨rv', hrel', k, hk⟩ := hR N rv m2 hrun
    exact ⟨rv', hrel', hmach _ ⟨k, hk⟩ (fun h => by cases h)⟩
  · obtain ⟨k, hk⟩ := hT N c hnmt hrun
    exact hmach _ ⟨k, hk⟩ (fun h => by cases h)
  · obtain ⟨k, hk⟩ := hU' N e m2 hrun
    exact hmach _ ⟨k, hk⟩ (fun h => by cases h)

end Front
