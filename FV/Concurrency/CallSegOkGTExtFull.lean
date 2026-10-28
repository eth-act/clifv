import FV.Concurrency.CallSegOkGTExtWitness

/-!
# The caller of an external through the generic call theorem, end to end (#649)

`realizes_linked_calls_ext` with every premise discharged but the run, on the link `linkX` of
`CallSegOkGTExtWitness` (the compiled caller `fC`, the external `ld` whose code is one `ret` and
whose specification `fX` returns its argument), as `WitnessFull.realizes_call_fullT` for the
compiled callee: one thread, the caller's root activation entered at its ABI entry `sC0` with a
callee budget of `0x200` bytes, its CLIF entry state `WitnessFull.csO`, in the environment without
externs.

* `wf_RAX`, `codeIn_RAX`: the activation is well formed and keeps the linked code (the external's
  one word is the compiled `atomic_load`'s last word, held by the caller's memory);
* **`shape_X`** (`WitnessFull.CallShape`): `csO` calls the specification `fX`, whose block is
  one `bor` and a `return`; **`partsOk_X`** (no access), **`depth_X`** (`depthG`);
* **`ent_X`**: the activation's `Ent` (`Live`, and `ChainP` by `chainP_entry`);
* **`realizes_call_extT`**: `realizes_linked_calls_ext` on `linkX`/`pX`, the external under its
  (here proven) contract `extX`, every premise discharged but the run.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.WitnessExt

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallComposeT CallSegOkG CallSegLive
  CallSegRun CallSegCall CallSeg.WitnessC RealizeCompiled.WitnessL ClifLift CallSegOkGT.Witness
  CallSegOkGT.WitnessFull PrepThread

/-! ## The caller's root activation in `linkX` -/

/-- The caller in `linkX` with a callee budget of `0x200` bytes. -/
abbrev RAX : RL := linkX.act callerF sC0 0x200 GL

theorem wf_RAX : RAX.Wf :=
  ⟨wf_RA5.check, wf_RA5.alloc, wf_RA5.emit, wf_RA5.layout, wf_RA5.lm, wf_RA5.fit, wf_RA5.stack,
    wf_RA5.psF, wf_RA5.prog0, wf_RA5.gfree⟩

/-- **The linked code is kept by the caller**: its own code, and the external's one word at
`retBase`, which is the compiled `atomic_load`'s last word in the caller's kept addresses. -/
theorem codeIn_RAX : CodeIn linkX RAX := by
  intro n FB hB
  rcases mem_linkX hB with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine .inr fun k wd hk => ?_
    have hk' : retFb.words[k]? = some wd := hk
    rw [checksX.2.2.1] at hk'
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ 0xd65f03c0#32 = wd := by
      cases k with
      | zero => simpa using hk'
      | succ k => simp at hk'
    have e : idF.base + BitVec.ofNat 64 (4 * 0) = ldF.base + BitVec.ofNat 64 (4 * 46) := by
      decide
    rw [e]
    rcases codeIn_RA5 "ld" ldF (.head _) with ⟨-, hb⟩ | h
    · exact absurd hb (by decide)
    · exact h 46 _ checksX.2.2.2.1
  · exact .inl ⟨rfl, rfl⟩

theorem body_RAX : BodyEntryW RAX.F RAX.vc.EntryArg RAX.af RAX.s0 w₀C := body_RA5

theorem relW_X : RelW ⟨RAX.F, fun _ => none, RAX.ctx.slotBase, 0⟩ fC (E2E.spv w₀C) [] memO
    w₀C := relW_O

theorem argsAt_X : ArgsAtEntry RAX.F fC.sig argsL w₀C := argsAt_O

theorem linv_X : Clif.LInv pX csO :=
  ⟨⟨List.mem_cons_self .., .inl ⟨B0C, List.mem_of_getElem? b0C, List.suffix_refl _, rfl⟩⟩,
    fun _ h => nomatch h⟩

theorem func_fCX : pX.func? "f" = some fC := by
  simp [Clif.Program.func?, pX, name_fC]

/-! ## The reachable CLIF states of `csO` in `pX` -/

/-- The specification's entry registers: `v0 = 0`. -/
def regsX : Clif.Regs :=
  (Clif.Regs.empty.setMany (B0X.params.map (·.1)) argsL).getD Clif.Regs.empty

/-- The specification entered from the caller's call. -/
def eFX : Clif.Frame := ⟨fX, regsX, [], B0X.body, B0X.term⟩

theorem checksFX : (Clif.AbiParam.tys fX.sig.params == Clif.AbiParam.tys extF.sig.params &&
      Clif.AbiParam.tys fX.sig.returns == Clif.AbiParam.tys extF.sig.returns) = true ∧
    fX.entry? = some B0X ∧ argsL.map (·.ty) = Clif.AbiParam.tys fX.sig.params ∧
    argsL.map (·.ty) = B0X.params.map (·.2) ∧
    (Clif.Regs.empty.setMany (B0X.params.map (·.1)) argsL).isSome = true := by
  native_decide -- witness: native_decide

theorem regsX_eq : Clif.Regs.empty.setMany (B0X.params.map (·.1)) argsL = some regsX := by
  have h := checksFX.2.2.2.2
  unfold regsX
  revert h
  cases Clif.Regs.empty.setMany (B0X.params.map (·.1)) argsL with
  | none => intro h; cases h
  | some r => intro _; rfl

/-- **`csO` calls the external's specification**: a `bor`, then both return. -/
theorem shape_X : CallShape pX csO eFX extC := by
  obtain ⟨hsig, hent, h1, h2, -⟩ := checksFX
  exact ⟨⟨rfl, fun _ hx => hx⟩, ⟨[1], 0, [0], extF, argsL, B0X, regsX, clifC.1, rfl, preC,
    func_fX, hsig, hent, h1, h2, regsX_eq, slots_fX, rfl⟩, ⟨_, body_B0X, (fun _ _ h => by cases h),
    (fun _ _ _ h => by cases h)⟩, ⟨_, term_B0X⟩, ⟨_, checksO.2.2.2.2.2.2.2.1⟩⟩

theorem evShape_eFX : evShape { csO with frame := eFX } = [[]] := by
  unfold evShape
  rw [show ({ csO with frame := eFX } : Clif.State).frame.body = B0X.body from rfl, body_B0X]

/-- **No access from the reachable states** (the specification's `bor` has no event): every
access lies on `LocO`. -/
theorem partsOk_X {env : Clif.Env} : PartsOk env pX (.run csO) LocO :=
  partsOkG shape_X (eS := { csO with frame := eFX }) rfl evShape_eFX (by simp)

/-- **At most one caller** below every reachable state. -/
theorem depth_X {env : Clif.Env} :
    ∀ S, RReach env pX (.run csO) (.run S) → S.callers.length < 2 :=
  depthG shape_X

/-! ## The activation's entry and the program-level statement -/

/-- **The caller's root activation in `linkX` entered at its ABI entry** (module doc). -/
theorem ent_X : ∃ g : Act, Ent linkX Clif.Env.empty pX (PrivA RAX) (.run csO) LocO fr2 Mx2 2
    (fun _ => none) g (sC0, none) (csT, PrivA RAX) := by
  obtain ⟨-, -, -, vc, ctx, st0, R, gn, bl, A, Lp, ss, ss', cc, ins, a0, hF⟩ :=
    fnOk_CX (env := Clif.Env.empty) rfl
  have hS := hF sC0 0x200 GL 0x4000#64 (E2E.spv w₀C) [] [] callerF [] (fun _ => False) [] wf_RAX
    abiRC checksO.2.2.2.2.2.2.2.2
  obtain ⟨-, hq, hA⟩ := q_init_lines wf_RAX abiRC body_RAX
  refine ⟨⟨"f", callerF, sC0, 0x200, GL, 0x4000#64, fC, vc, ctx, st0, R, gn, bl, A,
    ⟨RAX.F, fun _ => none, RAX.ctx.slotBase, 0⟩, E2E.spv w₀C, Lp, ss, ss', cc, ins, a0, [], [],
    callerF, [], fun _ => False, []⟩, rfl, csO, fun _ => False, rfl, ?_, ?_, func_fCX⟩
  · exact {
      stat := hS
      syms := rfl
      code := codeIn_RAX
      bnd := fun _ h => h
      dirty := fun _ h => .inl h
      reach := RReach.base
      call := rfl
      ret := fun h => absurd rfl h
      linv := linv_X
      place := rfl
      nv := fun _ _ _ _ h => h
      ndead := fun _ h => h.elim
      opens := fun _ h => absurd h List.not_mem_nil
      budget := show (2 - 0) * 240 ≤ 512 by decide
      func := rfl }
  · exact chainP_entry hS b0C rfl rfl rfl rfl rfl regsC_eq checksO.2.2.1 checksO.2.2.2.1 relW_X
      argsAt_X hq hA

open ProgE2E PrivCohT Rel in
/-- **The caller of an external through the call and back, from the generic theorem**
(`realizes_linked_calls_ext` on `linkX`/`pX` with one thread, the caller's root activation, the
external under its contract `extX`, every premise discharged but the run): every execution of the
realized prefix of a precise run of the linked machine from the caller's ABI entry is realized by
a `CStepS` thread of `pX` from `csO`. -/
theorem realizes_call_extT {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm linkX.M (OkB (PrivA RAX)) (sC0, none) ls t') :
    ∃ k : Nat → Nat, (∀ i < 1, k i ≤ ls.length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Concurrency.Rel PEv), PA.n = 1 →
        (∀ i < 1, PA.tr i = conv (evTr (ls.take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com) →
        InitFirst (PA.exec locsA rfA coA rmwA) →
        (∀ i < 1, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr (ls.take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < 1, PrivA RAX (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun _ l => PrivA RAX l ∨ PrivA RAX l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = csT) ∧ PC.Runs (CStepS Clif.Env.empty pX) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  obtain ⟨g, hg⟩ := ent_X
  exact realizes_linked_calls_ext (env := Clif.Env.empty) (n := 1) (Bnd := fun _ => PrivA RAX)
    (c0 := fun _ => .run csO) (Loc := fun _ => LocO) (Dcap := fun _ => 2) (g := fun _ => g)
    (sA := fun _ => (sC0, none)) (cs := fun _ => csT) (D0 := fun _ => PrivA RAX)
    (fun _ _ => partsOk_X) (fun _ _ => partDisj_O) linkFreeX keepsAllocs_E keepsPlace_E placeOkX
    (fun _ _ => depth_X) (linkOkX rfl) extX (fun _ _ => hg) (ls := fun _ => ls)
    (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSegOkGT.WitnessExt
