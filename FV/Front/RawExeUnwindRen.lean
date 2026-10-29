module

public import FV.Front.RawExeUnwind
public import FV.Front.RenameRunX

@[expose] public section

/-!
# The exceptional edges on cg_clif's program, without `i128` (S10f)

`bundle_correct_raw_unwind_ren`: when no function of the bundle's program mentions `i128`
(legalisation is the identity, `Opt.Legal.Complete.legalize_of_not_mentions`), the compiled
program is cg_clif's program `rawLink us sc` under the linked names (`σ`), and by renaming
invariance of the runs with unwinding (`Clif.runLoopX_ren`) the linked machine with unwinding
of an executable `compileExeU` writes refines **cg_clif's program's run with unwinding** of `f`
in cg_clif's environment `E` (`L.envX = E.ren σ`), its memories renamed to the linked names: a
return, a trap, or an exception leaving `f`.

With `i128` the compiled program is the legalised one; `FV/Front/RawExeUnwindSrc.lean`
(`bundle_correct_raw_unwind_src`) carries its runs with unwinding back to the original program
through the program-level legalisation theorem with unwinding
(`E2E.LegalProgram.legalProg_refinesX`).
-/

namespace Front

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary Link Opt.Legalize128 Backend Backend.Proof
  Backend.Proof.Driver

/-- `ArmRefinesU` does not read `stuck`'s message. -/
theorem armRefinesU_erase {fb : Backend.FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {o o' : XOutcome}
    (he : o.erase = o'.erase) (h : ArmRefinesU fb base ra astep s o) :
    ArmRefinesU fb base ra astep s o' := by
  cases o <;> cases o' <;> simp_all [XOutcome.erase] <;> trivial

/-- Without `i128`, the compiled program is cg_clif's program under the linked names. -/
theorem prog_raw {b : Bundle} {S : LinkSpec} (hb : buildSpec b = .ok S)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (hno : ∀ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = false) :
    prog S.inputCleanup = (rawLink us sc).rename σ.fwd := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  have hP : S.inputCleanup.srcProg = (rawLink us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hm : S.inputCleanup.srcProg.funcs.map legalize = S.inputCleanup.srcProg.funcs :=
    (List.map_congr_left fun g hg => Opt.Legal.Complete.legalize_of_not_mentions (hno g hg)).trans
      (List.map_id _)
  rw [Link.DeadCleanup.prog_eq_legal, ← hP]
  show { S.inputCleanup.srcProg with funcs := S.inputCleanup.srcProg.funcs.map legalize } = _
  rw [hm]

/-- **The shipped executable compiler with the unwind tables checked refines cg_clif's
program's runs with unwinding** (no `i128`): for `f` of cg_clif's program `rawLink us sc`
entered in `cs`, its compiled function `f.rename σ.fwd`, the linked program with unwinding `L`
of the input whose CLIF environment is cg_clif's `E` under the linked names, and the premises of
`compileExe_correct_unwind` for the compiled entry `cs.ren σ`: the unwinder reads every compiled
function's tables from `file`, and the linked machine with unwinding refines cg_clif's run of
`f`, its memories renamed (`XOutcome.ren σ`). -/
theorem bundle_correct_raw_unwind_ren {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (hno : ∀ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = false)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (E : XEnv) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hEX : L.envX = E.ren σ)
    (hbU : Link.DeadCleanup.BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Val}
    {cs : State}
    (hent : AbiEntry (L.A (f.rename σ.fwd)).fb (L.A (f.rename σ.fwd)).base ra s)
    (hres : StackAvail (κ M (f.rename σ.fwd)) (L.A (f.rename σ.fwd)).af s)
    (hFw : L.F = frameWG (κ M (f.rename σ.fwd))
      (RAFrame.compute (L.A (f.rename σ.fwd)).vcp (L.A (f.rename σ.fwd)).rf).intBase
      (RAFrame.compute (L.A (f.rename σ.fwd)).vcp (L.A (f.rename σ.fwd)).rf).size
      (L.A (f.rename σ.fwd)).af L.Img s)
    (hgfree : ∀ a, L.Img a →
      ¬ StackBelow (frameDrop (L.A (f.rename σ.fwd)).af + κ M (f.rename σ.fwd)) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A (f.rename σ.fwd)).af s w₀) (hargs : ArgsIn f.sig args s)
    (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A (f.rename σ.fwd)).af.slotBase,
      (RAFrame.compute (L.A (f.rename σ.fwd)).vcp (L.A (f.rename σ.fwd)).rf).intBase⟩
      (f.rename σ.fwd) (cs.ren σ).frame.slots (cs.ren σ).mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt (cs.ren σ).mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M (f.rename σ.fwd)) L.P.bare (cs.ren σ)) :
    (∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables)) ∧
      ArmRefinesU (L.A (f.rename σ.fwd)).fb (L.A (f.rename σ.fwd)).base ra
        (L.machU M (f.rename σ.fwd)) s
        ((runLoopX E (rawLink us sc) (M + 1) cs.toX).ren σ) := by
  have hP : L.P = (rawLink us sc).rename σ.fwd := by
    rw [hLs]; exact prog_raw hb hus hraw hσ hno
  have hfm : f.rename σ.fwd ∈ L.P.funcs := by
    have := Program.rename_func? σ (rawLink us sc) n
    rw [hf] at this
    rw [hP]; exact (Program.func?_some this).1
  obtain ⟨ht, hr⟩ := Link.DeadCleanup.compileExe_correct_unwind h B F hB hF L hLs hbU hNI hκ hfm M
    hent hres hFw hgfree himg hbe (by simpa using hargs) (clifEntry_ren hcs)
    (by simpa using hsav) hrel hpl htr
  refine ⟨ht, armRefinesU_erase ?_ hr⟩
  rw [hEX, hP, State.toX_ren]
  exact runLoopX_ren σ E (rawLink us sc) (M + 1) cs.toX

end Front
