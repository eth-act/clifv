import FV.E2E.Lockstep
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.RefinesCSem
import FV.Backend.Proof.IselContractP

/-! # The guarded semantics (agent/link-widen, stage 2)

`csemG F ctx X Rd syms exts sigs sp0 Pc`: `csem` where the memory accesses have the forms the memory rules use
and every byte read satisfies `Rd` (`GuardR`), and every call is one the pin `Pc` admits, with
its arguments where the ABI puts them in a world related to the pinned CLIF memory (`GuardC`,
`CallG`); undefined elsewhere. It satisfies the rule contracts with guarded reads and pinned
calls — `Refines`, `MemRefinesR Rd`, `CallsRefineP Pc`, `IndCallsRefineP Pc` — so the rules
instantiated with it (per CLIF step, with `Rd := ¬ Z` for the bytes `Z` where two worlds may
differ that the step's CLIF memory has not initialised, and `Pc` the step's CLIF call) give a
VCode run whose reads avoid `Z` and whose calls are the step's. Two such runs, on worlds that
agree outside `Z`, go in lockstep (`csemG_lockstep2`): the same outputs and control, worlds that
agree outside `Z` (`docs/contracts/e2e.md`, "Widening" item 2). -/

namespace E2E
open Backend Backend.Proof

/-- The guard of the reads of `csemG`: the memory accesses in the forms the memory rules use (an
addressing mode with an address, avoiding the frame `F`), every byte read satisfying `Rd`. -/
def GuardR (F Rd : BitVec 64 → Prop) (sb : Nat) : MInst → List CV → Arm.ArmState → Prop
  | .load op (.vreg _ .int) am _, us, w => op ≠ .fpuLoad128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a ∧
        ∀ k < op.bytes, Rd (a + BitVec.ofNat 64 k)
  | .store op (.vreg _ .int) am _, _ :: us, w => op ≠ .fpuStore128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _, [u], _ =>
      AtomTy ty ∧ Avoids F ty.bytes (lo64 u) ∧ ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _, [u, _], _ =>
      AtomTy ty ∧ Avoids F ty.bytes (lo64 u)
  | .atomicRmwLoop ty .., u :: _, _ => ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .atomicCasLoop ty .., u :: _, _ => ∀ k < ty.bytes, Rd (lo64 u + BitVec.ofNat 64 k)
  | .load .., _, _ | .store .., _, _ | .loadAcquire .., _, _ | .storeRelease .., _, _ => False
  | _, _, _ => True

/-- The callee name `csem` passes the external semantics (`bl name`; `none` for `blr`). -/
def destName : CallDest → Option String
  | .sym n => some n
  | .reg _ => none

/-- **A pinned call** from world `w` (destination `dest`, use values `uses`): the extern `n`,
signature `sig`, argument values `vals` and CLIF memory `cm` are admitted by `Pc`, `w` is related
to `cm` (`MemRel`) with stack pointer `sp0`, and the arguments are as the call's kind puts them: a call of a declared
extern (in `exts`, with its signature) has them where the ABI puts them (`ArgsAt`; the register
ones the uses, after the target of a `blr`, which holds `n`'s link-time address); an indirect
call (signature in `sigs`) has at most 8 values, all in registers. -/
def CallG (F : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (dest : CallDest)
    (uses : List CV) (w : Arm.ArmState) : Prop :=
  ∃ n sig vals cm args, Pc n sig vals cm ∧ (MemRel F syms cm w ∧ spv w = sp0) ∧
    ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∧ ArgsAt sig vals args w ∨
      sig ∈ sigs ∧ vals.length ≤ 8 ∧ AllHold vals args) ∧
    (dest = .sym n ∧ uses = args ∨ (∃ r, dest = .reg r) ∧ ∃ u, uses = u :: args ∧ lo64 u = X.sym n 0)

/-- The guard of the calls of `csemG`: a `call` and a `tryCall` are pinned (`CallG`); the entry's
`Args` (which the rules never emit) is excluded. -/
def GuardC (F : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    MInst → List CV → Arm.ArmState → Prop
  | .call info, us, w => CallG F syms X exts sigs sp0 Pc info.dest us w
  | .tryCall info _, us, w => CallG F syms X exts sigs sp0 Pc info.dest us w
  | .args _, _, _ => False
  | _, _, _ => True

open Classical in
/-- **The guarded semantics**: `csem` where `GuardR` and `GuardC` hold, undefined elsewhere. -/
noncomputable def csemG (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (Rd : BitVec 64 → Prop)
    (syms : String → Option Nat) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    Sem := fun i us w =>
  if GuardR F Rd ctx.slotBase i us w ∧ GuardC F syms X exts sigs sp0 Pc i us w then csem F ctx X i us w
  else none

variable {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {Rd : BitVec 64 → Prop}
  {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
  {sp0 : BitVec 64}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}

theorem csemG_of {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : GuardR F Rd ctx.slotBase i us w) (hc : GuardC F syms X exts sigs sp0 Pc i us w) :
    csemG F ctx X Rd syms exts sigs sp0 Pc i us w = csem F ctx X i us w := by
  simp [csemG, h, hc]

theorem csemG_sub {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemG F ctx X Rd syms exts sigs sp0 Pc i us w = some r) :
    GuardR F Rd ctx.slotBase i us w ∧ GuardC F syms X exts sigs sp0 Pc i us w ∧ csem F ctx X i us w = some r := by
  unfold csemG at h
  split at h
  · exact ⟨‹_ ∧ _›.1, ‹_ ∧ _›.2, h⟩
  · cases h

/-- The guard with `Rd` the complement of `Z` is the lockstep's guard (outside the forms it does
not cover). -/
theorem lockGuard_of {Z : BitVec 64 → Prop} {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : GuardR F (fun b => ¬ Z b) ctx.slotBase i us w)
    (hl : ∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e)
    (hc : ∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e)
    (ht : ∀ info ti, i ≠ .tryCall info ti) (ha : ∀ ds, i ≠ .args ds) :
    LockGuard F Z ctx.slotBase i us w := by
  unfold GuardR at h
  unfold LockGuard
  split at h
  all_goals first
    | exact h
    | exact h.elim
    | (exfalso; exact hl _ _ _ _ _ _ _ _ rfl)
    | (exfalso; exact hc _ _ _ _ _ _ _ rfl)
    | (split
       all_goals first
         | trivial
         | (exfalso; solve_by_elim)
         | (exfalso; exact hl _ _ _ _ _ _ _ _ rfl)
         | (exfalso; exact hc _ _ _ _ _ _ _ rfl)
         | (exfalso; exact ht _ _ rfl)
         | (exfalso; exact ha _ rfl))

/-- **The guarded semantics refines the memory forms with guarded reads** (`MemRefinesR Rd`). -/
theorem memRefinesR_csemG {sb : Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefinesR Rd F sb syms (csemG F ctx X Rd syms exts sigs sp0 Pc) := by
  have hM := memRefines_csem (F := F) (ctx := ctx) X hsb hsym
  subst hsb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op d am fl uses w a hop ha hav hrd
    have hg : GuardR F Rd ctx.slotBase (.load op (.vreg d .int) am fl) uses w := ⟨hop, a, ha, hav, hrd⟩
    have hc : GuardC F syms X exts sigs sp0 Pc (.load op (.vreg d .int) am fl) uses w := trivial
    rw [csemG_of hg hc]
    exact hM.1 op d am fl uses w a hop ha hav
  · intro op d am fl v uses w a hop ha hav
    have hg : GuardR F Rd ctx.slotBase (.store op (.vreg d .int) am fl) (v :: uses) w :=
      ⟨hop, a, ha, hav⟩
    have hc : GuardC F syms X exts sigs sp0 Pc (.store op (.vreg d .int) am fl) (v :: uses) w := trivial
    rw [csemG_of hg hc]
    exact hM.2.1 op d am fl v uses w a hop ha hav
  · intro d off w
    have hg : GuardR F Rd ctx.slotBase (.loadAddr (.vreg d .int) (.slotOffset off)) [] w := trivial
    have hc : GuardC F syms X exts sigs sp0 Pc (.loadAddr (.vreg d .int) (.slotOffset off)) [] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.1 d off w
  · intro d n b w hb
    have hg : GuardR F Rd ctx.slotBase (.loadExtNameGot (.vreg d .int) n) [] w := trivial
    have hc : GuardC F syms X exts sigs sp0 Pc (.loadExtNameGot (.vreg d .int) n) [] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.1 d n b w hb
  · intro ty d r fl u w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.loadAcquire ty (.vreg d .int) (.vreg r .int) fl) [u] w :=
      ⟨hty, hav, hrd⟩
    have hc : GuardC F syms X exts sigs sp0 Pc (.loadAcquire ty (.vreg d .int) (.vreg r .int) fl) [u] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.2.1 ty d r fl u w hty hav
  · intro ty d r fl u v w hty hav
    have hg : GuardR F Rd ctx.slotBase (.storeRelease ty (.vreg d .int) (.vreg r .int) fl) [u, v] w :=
      ⟨hty, hav⟩
    have hc : GuardC F syms X exts sigs sp0 Pc (.storeRelease ty (.vreg d .int) (.vreg r .int) fl) [u, v] w :=
      trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.2.2.1 ty d r fl u v w hty hav
  · intro ty op fl ra ro rd r1 r2 u x w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.atomicRmwLoop ty op fl (.vreg ra .int) (.vreg ro .int)
      (.vreg rd .int) (.vreg r1 .int) (.vreg r2 .int)) [u, x] w := hrd
    have hc : GuardC F syms X exts sigs sp0 Pc (.atomicRmwLoop ty op fl (.vreg ra .int) (.vreg ro .int)
      (.vreg rd .int) (.vreg r1 .int) (.vreg r2 .int)) [u, x] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.2.2.2.1 ty op fl ra ro rd r1 r2 u x w hty hav
  · intro ty fl ra re rx rd r1 u e x w hty hav hrd
    have hg : GuardR F Rd ctx.slotBase (.atomicCasLoop ty fl (.vreg ra .int) (.vreg re .int)
      (.vreg rx .int) (.vreg rd .int) (.vreg r1 .int)) [u, e, x] w := hrd
    have hc : GuardC F syms X exts sigs sp0 Pc (.atomicCasLoop ty fl (.vreg ra .int) (.vreg re .int)
      (.vreg rx .int) (.vreg rd .int) (.vreg r1 .int)) [u, e, x] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.2.2.2.2.1 ty fl ra re rx rd r1 u e x w hty hav
  · intro d t n b w hb
    have hg : GuardR F Rd ctx.slotBase (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)) [] w := trivial
    have hc : GuardC F syms X exts sigs sp0 Pc (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)) [] w := trivial
    rw [csemG_of hg hc]
    exact hM.2.2.2.2.2.2.2.2 d t n b w hb

/-- The forms `ispec` specifies are not memory forms or calls: the guards hold there. -/
theorem guards_of_ispec {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : ispec i us w = some r) (sb : Nat) :
    GuardR F Rd sb i us w ∧ GuardC F syms X exts sigs sp0 Pc i us w := by
  constructor
  · unfold GuardR
    split
    all_goals first
      | trivial
      | (simp [ispec] at h)
      | (exfalso; revert h; simp [ispec])
  · unfold GuardC
    split
    all_goals first
      | trivial
      | (simp [ispec] at h)

theorem refines_csemG : Refines F (csemG F ctx X Rd syms exts sigs sp0 Pc) := by
  intro i us w outs w' ctl h
  obtain ⟨h1, h2⟩ := guards_of_ispec (F := F) (Rd := Rd) (syms := syms) (X := X) (exts := exts)
    (sigs := sigs) (sp0 := sp0) (Pc := Pc) h ctx.slotBase
  rw [csemG_of h1 h2]
  exact refines_csem F ctx X i us w outs w' h

theorem lo64_ofX64 (x : BitVec 64) : lo64 (ofX x) = x := by
  simp [lo64, ofX, BitVec.setWidth_setWidth_of_le]

/-- **The pinned callee contract for the guarded semantics**, from the external contract and
the memory relation's `MemRel`. -/
theorem callsRefineP_csemG {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    CallsRefineP Pc F env exts MR (csemG F ctx X Rd syms exts sigs sp0 Pc) := by
  refine ⟨fun n => X.sym n 0, fun rd n w => ?_, fun ext hin g sl cm w dest us ds uses args vals
    rvals cm' a1 a2 a3 a4 a5 hpc a7 a8 => ?_, fun ext hin g sl cm w dest us ds ti uses args vals
    rvals cm' a1 a2 a3 a0 a4 a5 hpc a7 a8 => ?_⟩
  · have hg : GuardR F Rd ctx.slotBase (.loadExtNameGot rd n) [] w := by
      unfold GuardR; split <;> simp_all
    have hc : GuardC F syms X exts sigs sp0 Pc (.loadExtNameGot rd n) [] w := trivial
    rw [csemG_of hg hc]
    exact ⟨w, rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩
  · have hg : GuardR F Rd ctx.slotBase (.call ⟨dest, us, ds⟩) uses w := trivial
    have hc : GuardC F syms X exts sigs sp0 Pc (.call ⟨dest, us, ds⟩) uses w := by
      refine ⟨ext.name, ext.sig, vals, cm, args, hpc, ⟨hMRm sl cm w a5, hMRc sl cm w a5⟩, .inl ⟨⟨ext, hin, rfl, rfl⟩, a4⟩, ?_⟩
      rcases a2 with ⟨rfl, rfl⟩ | ⟨r, rfl, -, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨⟨r, rfl⟩, _, rfl, lo64_ofX64 _⟩
    rw [csemG_of hg hc]
    rcases a2 with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩
    · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w (some ext.name) uses uses vals rvals
        cm' a1 (.inl ⟨rfl, rfl⟩) a4 a5 a7 a8
      exact ⟨outs, w', by simp [csem, hc], by rw [hol, a3], ho, hm⟩
    · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w none _ args vals rvals cm'
        a1 (.inr ⟨rfl, hcol, rfl⟩) a4 a5 a7 a8
      exact ⟨outs, w', by simp [csem, hc], by rw [hol, a3], ho, hm⟩
  · have hg : GuardR F Rd ctx.slotBase (.tryCall ⟨dest, us, ds⟩ ti) uses w := trivial
    have hc : GuardC F syms X exts sigs sp0 Pc (.tryCall ⟨dest, us, ds⟩ ti) uses w := by
      refine ⟨ext.name, ext.sig, vals, cm, args, hpc, ⟨hMRm sl cm w a5, hMRc sl cm w a5⟩, .inl ⟨⟨ext, hin, rfl, rfl⟩, a4⟩, ?_⟩
      rcases a2 with ⟨rfl, rfl⟩ | ⟨r, rfl, -, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨⟨r, rfl⟩, _, rfl, lo64_ofX64 _⟩
    rw [csemG_of hg hc]
    rcases a2 with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩
    · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w (some ext.name) uses uses vals
        rvals cm' a1 (.inl ⟨rfl, rfl⟩) a4 a5 a7 a8
      refine ⟨_, w', by simp only [csem, hc, Option.filter_some, hol, a0, decide_true, ↓reduceIte,
        Option.map_some]; rfl, ?_, ho.append _, hm⟩
      simp only [List.length_append, List.length_map, List.length_drop]
      omega
    · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w none _ args vals rvals cm' a1
        (.inr ⟨rfl, hcol, rfl⟩) a4 a5 a7 a8
      refine ⟨_, w', by simp only [csem, hc, Option.filter_some, hol, a0, decide_true, ↓reduceIte,
        Option.map_some]; rfl, ?_, ho.append _, hm⟩
      simp only [List.length_append, List.length_map, List.length_drop]
      omega

/-- **The pinned indirect-call contract for the guarded semantics.** -/
theorem indCallsRefineP_csemG {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0) :
    IndCallsRefineP Pc env sigs MR (csemG F ctx X Rd syms exts sigs sp0 Pc) := by
  obtain ⟨h1, h2⟩ := indCallsRefine_csem (F := F) (ctx := ctx) hX hsym
    (fun sl cm w h => (hMRm sl cm w h).symbols)
  refine ⟨fun sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a1' a2 a3 a4 a5 a6 a7 hpc a9
    a10 a11 => ?_, fun sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a1' a2 a3 a4 a0 a5
    a6 a7 hpc a9 a10 a11 => ?_⟩
  · have hm := hMRm sl cm w a7
    have hu : lo64 u = X.sym n 0 := by
      rw [a3, hsym n a (by rw [← hm.symbols]; exact a2)]
    have hg : GuardC F syms X exts sigs sp0 Pc (.call ⟨.reg r, us, ds⟩) (u :: args) w :=
      ⟨n, sig, vals, cm, args, hpc, ⟨hm, hMRc sl cm w a7⟩, (.inr ⟨hin, a5, a6⟩), .inr ⟨⟨r, rfl⟩, u, rfl, hu⟩⟩
    have hr : GuardR F Rd ctx.slotBase (.call ⟨.reg r, us, ds⟩) (u :: args) w := trivial
    rw [csemG_of hr hg]
    exact h1 sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a1' a2 a3 a4 a5 a6 a7 a9 a10 a11
  · have hm := hMRm sl cm w a7
    have hu : lo64 u = X.sym n 0 := by
      rw [a3, hsym n a (by rw [← hm.symbols]; exact a2)]
    have hg : GuardC F syms X exts sigs sp0 Pc (.tryCall ⟨.reg r, us, ds⟩ ti) (u :: args) w :=
      ⟨n, sig, vals, cm, args, hpc, ⟨hm, hMRc sl cm w a7⟩, (.inr ⟨hin, a5, a6⟩), .inr ⟨⟨r, rfl⟩, u, rfl, hu⟩⟩
    have hr : GuardR F Rd ctx.slotBase (.tryCall ⟨.reg r, us, ds⟩ ti) (u :: args) w := trivial
    rw [csemG_of hr hg]
    exact h2 sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a1' a2 a3 a4 a0 a5 a6 a7 a9 a10
      a11

theorem minst_cases (i : MInst) :
    (∃ info, i = .call info) ∨ (∃ info ti, i = .tryCall info ti) ∨ (∃ ds, i = .args ds) ∨
    (∃ ty op fl a b c d e, i = .atomicRmwLoop ty op fl a b c d e) ∨
    (∃ ty fl a b c d e, i = .atomicCasLoop ty fl a b c d e) ∨
    ((∀ ty op fl a b c d e, i ≠ .atomicRmwLoop ty op fl a b c d e) ∧
      (∀ ty fl a b c d e, i ≠ .atomicCasLoop ty fl a b c d e) ∧
      (∀ info ti, i ≠ .tryCall info ti) ∧ (∀ ds, i ≠ .args ds) ∧ (∀ info, i ≠ .call info)) := by
  cases i <;> simp

/-- **Two guarded runs of one instruction, in lockstep**: where `csemG` with the reads guarded
by `¬ Z` runs an instruction on two worlds that agree outside `Z ⊇ F`, with callees (of the
pinned calls, `hX`) and the TLSDESC resolver (`hT`) that keep the agreement: the same outputs
and control, worlds that agree outside `Z`. -/
theorem csemG_lockstep2 {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {i : MInst} {us : List CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hX : ∀ dest, CallG F syms X exts sigs sp0 Pc dest us w → CallG F syms X exts sigs sp0 Pc dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {c c' : Ctl}
    (h : csemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w = some (o, w₁, c))
    (h' : csemG F ctx X (fun b => ¬ Z b) syms exts sigs sp0 Pc i us w' = some (o', w₁', c')) :
    o = o' ∧ c = c' ∧ SameWorld Z w₁ w₁' := by
  obtain ⟨hg, hgc, hs⟩ := csemG_sub h
  obtain ⟨-, hgc', hs'⟩ := csemG_sub h'
  have hav : ∀ {n : Nat} {a : BitVec 64}, (∀ k < n, ¬ Z (a + BitVec.ofNat 64 k)) → Avoids Z n a :=
    fun h k hk hz => h k hk hz
  have hdest : ∀ dest : CallDest, ∀ {r : Option (List CV × Arm.ArmState)},
      X.call (match dest with | .sym n => some n | .reg _ => none) us w = r →
      X.call (destName dest) us w = r := by
    intro dest r h; cases dest <;> exact h
  have hdest' : ∀ dest : CallDest, ∀ {r : Option (List CV × Arm.ArmState)},
      X.call (match dest with | .sym n => some n | .reg _ => none) us w' = r →
      X.call (destName dest) us w' = r := by
    intro dest r h; cases dest <;> exact h
  rcases minst_cases i with ⟨info, rfl⟩ | ⟨info, ti, rfl⟩ | ⟨ds, rfl⟩ |
    ⟨ty, op, fl, a, b, c0, d, e, rfl⟩ | ⟨ty, fl, a, b, c0, d, e, rfl⟩ | ⟨hl, hc, ht, ha, hcl⟩
  · simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hs hs'
    obtain ⟨⟨o1, x1⟩, hp, rfl, rfl, rfl⟩ := hs
    obtain ⟨⟨o2, x2⟩, hp', rfl, rfl, rfl⟩ := hs'
    obtain ⟨ho, hx⟩ := hX info.dest hgc hgc' _ _ _ _ (hdest _ hp) (hdest' _ hp')
    exact ⟨ho, rfl, hx⟩
  · simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff, Prod.mk.injEq] at hs hs'
    obtain ⟨⟨o1, x1⟩, ⟨hp, -⟩, rfl, rfl, rfl⟩ := hs
    obtain ⟨⟨o2, x2⟩, ⟨hp', -⟩, rfl, rfl, rfl⟩ := hs'
    obtain ⟨ho, hx⟩ := hX info.dest hgc hgc' _ _ _ _ (hdest _ hp) (hdest' _ hp')
    subst ho
    exact ⟨rfl, rfl, hx⟩
  · exact hgc.elim
  · match us, hg, hs, hs' with
    | [u, x], hg, hs, hs' => exact rmw_lockstep2 hw (hav hg) hs hs'
    | [], _, hs, _ => simp [csem] at hs
    | [_], _, hs, _ => simp [csem] at hs
    | _ :: _ :: _ :: _, _, hs, _ => simp [csem] at hs
  · match us, hg, hs, hs' with
    | [u, v, x], hg, hs, hs' => exact cas_lockstep2 hw (hav hg) hs hs'
    | [], _, hs, _ => simp [csem] at hs
    | [_], _, hs, _ => simp [csem] at hs
    | [_, _], _, hs, _ => simp [csem] at hs
    | _ :: _ :: _ :: _ :: _, _, hs, _ => simp [csem] at hs
  · obtain ⟨w₂, h2, hsw⟩ := csem_lockstep hFZ hw (lockGuard_of hg hl hc ht ha)
      (fun info hi => absurd hi (hcl info)) hT hs
    rw [hs'] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨rfl, rfl, SameWorld.mono (fun _ hb => hb.1) hsw⟩

end E2E
