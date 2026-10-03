import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.MemRefines

/-! # Lockstep of `csem` on two worlds (agent/link-widen, stage 2)

Linking callees with stack slots or an outgoing-argument area needs **non-interference**: the
callee's VCode outcome must not depend on the bytes its two body-entry worlds (from the
canonical and the actual caller state) disagree on — CLIF-uninitialised slot bytes and the
outgoing area (`docs/contracts/e2e.md`, "Widening" item 2). The route runs the (world-generic)
driver on pairs of worlds; its per-step facts come from the memory rules' read footprint
(`MemRulesCorrectR`) and from this file:

* `csem_lockstep`: one instruction of `csem F ctx X` on two worlds that agree outside `Z ⊇ F`
  (`SameWorld Z`), whose reads avoid `Z` (`LockGuard`), with callees and the TLSDESC resolver
  that keep the agreement: the same outputs and control, and worlds that agree outside `Z` minus
  the bytes it writes (`WriteSet`).
* The straight-line forms without memory access go through M6's per-form obligation
  (`formOk_sound`, `OperandsSound Z`) at the canonical registers, which pass the allocation
  checker's static checks (`canon_facts`, decided per form); the memory forms through their
  `MemRefines` characterisations (`csem_load` …); `ispec`/`mspec` and the control forms read the
  world only through the flags, `sp` and `x29`.

Not covered yet: the LL/SC loops (their scratch defs), `try_call` (`csem` gives its payload defs
from the callee's world) and `Args` (the entry). -/

open Backend Backend.Proof

/-- The memory-access forms (their canonical runs read or write memory). -/
def _root_.Backend.MInst.isMemAcc : Backend.MInst → Bool
  | .load .. | .store .. | .loadAcquire .. | .storeRelease .. => true
  | _ => false

namespace E2E

/-- A checker context (the static checks of one instruction do not read it for registers). -/
def checkCtx0 : CheckCtx := ⟨default, #[], default, 0⟩

theorem sameWorld_flag {Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (h : SameWorld Z w w') :
    ∀ c, Arm.ConditionHolds c w = Arm.ConditionHolds c w' := ConditionHolds_sameWorld h

theorem SameWorld.write_pstate' {Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (h : SameWorld Z w w')
    (p : Arm.PState) : SameWorld Z (Arm.write_pstate p w) (Arm.write_pstate p w') := by
  unfold Arm.write_pstate
  exact SameWorld.w_both (SameWorld.w_both (SameWorld.w_both (SameWorld.w_both h)))

theorem condBrHolds_sameWorld {Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (k : CondBrKind) (us : List CV) : condBrHolds k us w = condBrHolds k us w' := by
  unfold condBrHolds
  split <;> simp [ConditionHolds_sameWorld hw]

set_option maxHeartbeats 4000000 in
/-- `ispec` reads the world only through the flags and returns it or rewrites its flags. -/
theorem ispec_lockstep {Z : BitVec 64 → Prop} {i : MInst} {us : List CV} {w w' : Arm.ArmState}
    (hw : SameWorld Z w w') {o : List CV} {w₁ : Arm.ArmState} {c : Ctl}
    (h : ispec i us w = some (o, w₁, c)) :
    ∃ w₁', ispec i us w' = some (o, w₁', c) ∧ SameWorld Z w₁ w₁' := by
  have hc := sameWorld_flag hw
  unfold ispec at h ⊢
  split at h
  all_goals (try simp only [hc, condBrHolds_sameWorld hw] at h ⊢)
  all_goals (
    try simp only [Option.ite_none_right_eq_some, Option.ite_none_left_eq_some,
      Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    first
    | (cases h; done)
    | (obtain ⟨rfl, rfl, rfl⟩ := h
       exact ⟨_, rfl, by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (obtain ⟨hp, rfl, rfl, rfl⟩ := h
       exact ⟨_, by rw [if_pos hp], by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (obtain ⟨r, hr, rfl, rfl, rfl⟩ := h
       exact ⟨_, by rw [hr]; rfl, by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (obtain ⟨hp, r, hr, rfl, rfl, rfl⟩ := h
       exact ⟨_, by rw [if_pos hp, hr]; rfl, by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (obtain ⟨hp, r, hr, rfl, rfl, rfl⟩ := h
       exact ⟨_, by rw [if_neg hp, hr]; rfl, by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (obtain ⟨hp, rfl, rfl, rfl⟩ := h
       exact ⟨_, by rw [if_neg hp], by first | exact hw | exact SameWorld.write_pstate' hw _⟩)
    | (have hw1 : w₁ = w := by
         revert h; split <;> (try split) <;> intro h <;> simp only [Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq] at h <;> exact h.2.1.symm
       subst hw1
       refine ⟨w', ?_, hw⟩
       revert h; split <;> (try split) <;> intro h <;> simp only [Option.some.injEq,
           Prod.mk.injEq, reduceCtorEq] at h <;> obtain ⟨rfl, -, rfl⟩ := h <;> rfl)
)

/-- A register that `setReg`/`regVal` treat as a plain X or V register. -/
def PlainReg (r : Reg) : Prop := (∃ n, n < 32 ∧ r = .x n) ∨ (∃ n, n < 32 ∧ r = .v n)

/-- The value `regVal` reads back after `setReg` of `u`. -/
def normVal : Reg → CV → CV
  | .x _, u => (lo64 u).setWidth 128
  | _, u => u

theorem regVal_setReg_self {r : Reg} (hr : PlainReg r) (s : Arm.ArmState) (u : CV) :
    regVal (setReg s r u) r = normVal r u := by
  rcases hr with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ <;> simp [regVal, normVal]

theorem setReg_normVal {r : Reg} (hr : PlainReg r) (s : Arm.ArmState) (u : CV) :
    setReg s r (normVal r u) = setReg s r u := by
  rcases hr with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · simp only [normVal, setReg_x, lo64]
    congr 1
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_setWidth, hi, show i < 128 by omega]
  · rfl

theorem regVal_setReg_other {r r' : Reg} (hr : PlainReg r) (hr' : PlainReg r') (hne : r ≠ r')
    (s : Arm.ArmState) (u : CV) : regVal (setReg s r' u) r = regVal s r := by
  rcases hr with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ <;> rcases hr' with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ <;>
    simp only [regVal, setReg_x, setReg_v, r_gpr_w_gpr, r_sfp_w_sfp, r_gpr_w_sfp, r_sfp_w_gpr]
  · have : rnum n ≠ rnum m := rnum_ne hn hm (fun e => hne (by rw [e]))
    simp [this]
  · have : rnum n ≠ rnum m := rnum_ne hn hm (fun e => hne (by rw [e]))
    simp [this]

theorem regVal_foldl_other {r : Reg} (hr : PlainReg r) :
    ∀ (R : List Reg) (vs : List CV) (s : Arm.ArmState), (∀ r' ∈ R, PlainReg r') → r ∉ R →
      regVal ((R.zip vs).foldl (fun s p => setReg s p.1 p.2) s) r = regVal s r
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | r' :: R, v :: vs, s, hR, hn => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [regVal_foldl_other hr R vs _ (fun x hx => hR x (List.mem_cons_of_mem _ hx))
      (fun h => hn (List.mem_cons_of_mem _ h))]
    exact regVal_setReg_other hr (hR r' List.mem_cons_self) (fun e => hn (e ▸ List.mem_cons_self)) s v

/-- Writing values into distinct plain registers and reading them back gives values that write
the same registers. -/
theorem foldl_setReg_reads :
    ∀ (R : List Reg) (us : List CV) (t w : Arm.ArmState), R.Nodup → (∀ r ∈ R, PlainReg r) →
      R.length = us.length →
      (R.zip (R.map (regVal ((R.zip us).foldl (fun s p => setReg s p.1 p.2) t)))).foldl
          (fun s p => setReg s p.1 p.2) w =
        (R.zip us).foldl (fun s p => setReg s p.1 p.2) w
  | [], _, _, _, _, _, _ => by simp
  | _ :: _, [], _, _, _, _, h => by simp at h
  | r :: R, u :: us, t, w, hnd, hR, hlen => by
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    have hr : PlainReg r := hR r List.mem_cons_self
    have hR' : ∀ x ∈ R, PlainReg x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
    have hnr : r ∉ R := (List.nodup_cons.1 hnd).1
    rw [regVal_foldl_other hr R us _ hR' hnr, regVal_setReg_self hr, setReg_normVal hr]
    exact foldl_setReg_reads R us (setReg t r u) (setReg w r u) (List.nodup_cons.1 hnd).2 hR'
      (by simpa using hlen)


set_option maxHeartbeats 8000000 in
theorem canon_facts {ctx : FnCtx} {i : MInst} (h : FormOk ctx i = true) (hm : i.isMemAcc = false)
    (c : CheckCtx) :
    ∃ ops ic, i.operands = .ok ops ∧ i.assign (canonRegs ops) = .ok ic ∧
      c.checkStatic "" ops ((canonRegs ops).map Loc.reg) i.clobbers = .ok () ∧
      (∀ s, ic.accesses ctx s = []) ∧
      (((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2)).Nodup ∧
      ∀ r ∈ ((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2),
        (∃ n, n < 6 ∧ r = .x n) ∨ (∃ n, n < 32 ∧ r = .v n) := by
  unfold FormOk at h
  split at h
  all_goals first
    | (cases h; done)
    | (cases hm; done)
    | skip
  all_goals (
    refine ⟨_, _, rfl, rfl, ?_, fun s => ?_, ?_, ?_⟩
    rotate_left
    · rfl
    · simp (config := {decide := true}) [canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use,
        OpSpec.reuseDef, List.range, List.range.loop, Operand.isUse]
    · simp (config := {decide := true}) [canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use,
        OpSpec.reuseDef, List.range, List.range.loop, Operand.isUse]
    simp (config := {decide := true}) [CheckCtx.checkStatic, canonRegs, canonReg, canonBase,
      CheckCtx.checkOperand, CheckCtx.locOk, ensure, Loc.cls?, defConflicts, MInst.clobbers,
      OpSpec.def_, OpSpec.use, OpSpec.reuseDef, List.range, List.range.loop, List.zipIdx, forM, List.forM,
      Reg.allocatable, aarch64Env, bind, Except.bind, pure, Except.pure, Loc.isReg])


theorem placeUses_eq (ops : Array Operand) (regs : Array Reg) (uses : List CV) (w : Arm.ArmState) :
    placeUses ops regs uses w =
      ((((ops.zip regs).toList.filter (·.1.isUse)).map (·.2)).zip uses).foldl
        (fun s p => setReg s p.1 p.2) w := rfl

theorem useVals_eq (ops : Array Operand) (regs : Array Reg) (s : Arm.ArmState) :
    useVals ops regs s = (((ops.zip regs).toList.filter (·.1.isUse)).map (·.2)).map (regVal s) := by
  simp [useVals, List.map_map]

/-- Masked writes keep the world. -/
theorem sameWorld_foldl_setReg {Z : BitVec 64 → Prop} :
    ∀ (R : List Reg) (vs : List CV) (s t : Arm.ArmState),
      (∀ r ∈ R, (∃ n, n < 6 ∧ r = .x n) ∨ (∃ n, n < 32 ∧ r = .v n)) → SameWorld Z s t →
      SameWorld Z ((R.zip vs).foldl (fun s p => setReg s p.1 p.2) s) t
  | [], _, _, _, _, h => by simpa using h
  | _ :: _, [], _, _, _, h => by simpa using h
  | r :: R, v :: vs, s, t, hR, h => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    refine sameWorld_foldl_setReg R vs _ t (fun x hx => hR x (List.mem_cons_of_mem _ hx)) ?_
    rcases hR r List.mem_cons_self with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · exact SameWorld.w_left (by simp [Masked, rnum]; omega) h
    · exact SameWorld.w_left (by simp [Masked]) h

theorem map_eq_of_zip {α β : Type} {f : α → β} :
    ∀ (L : List α) (o : List β), L.length = o.length → (∀ p ∈ L.zip o, f p.1 = p.2) → L.map f = o
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: L, b :: o, h, hz => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hz (a, b) (by simp), map_eq_of_zip L o (by simpa using h)
      fun p hp => hz p (List.mem_cons_of_mem _ hp)⟩

set_option maxHeartbeats 1000000 in
/-- **The lockstep of a straight-line form without memory access**: the canonical run on two
worlds that agree outside `Z` gives the same defs and worlds that agree outside `Z`. -/
theorem straight_lockstep {F Z : BitVec 64 → Prop} {ctx : FnCtx} (X : ExtSem) {i : MInst}
    (hfo : FormOk ctx i = true) (hm : i.isMemAcc = false) (hctl : i.isCtl = false)
    {us : List CV} (hwf : csemWF ctx i us = true) {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (herr : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {o : List CV}
    {w₁ : Arm.ArmState} {c : Ctl} (h : straightSem F ctx i us w = some (o, w₁, c)) :
    ∃ w₁', straightSem F ctx i us w' = some (o, w₁', c) ∧ SameWorld Z w₁ w₁' := by
  obtain ⟨ops, ic, hops, hic, hcs, hacc, hnd, hpl⟩ := canon_facts hfo hm checkCtx0
  have hsz := canonRegs_size ops
  have hlen : us.length = useCount ops := (by simpa [csemWF, hops] using hwf : _ ∧ _).2
  have hA : ∀ G s, AccessOk G ctx ic s := fun G s p hp => by rw [hacc] at hp; cases hp
  let R := ((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2)
  have hRl : R.length = us.length := by
    rw [hlen]
    simp only [R, List.length_map, useCount, Array.toList_zip]
    exact len_filter_zip _ _ (by simp [hsz])
  have hplain : ∀ r ∈ R, PlainReg r := fun r hr => by
    rcases hpl r hr with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · exact .inl ⟨n, by omega, rfl⟩
    · exact .inr ⟨n, hn, rfl⟩
  -- the run on `w`
  simp only [straightSem, hops, hic] at h
  split at h
  · split at h
    · rename_i t' hex
      split at h
      · rename_i hok
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        -- the state with the uses placed on `w'`
        let P := placeUses ops (canonRegs ops) us w'
        have hPw' : SameWorld Z P w' := sameWorld_foldl_setReg R us w' w' hpl (SameWorld.refl _ _)
        have hPw : SameWorld Z P w := hPw'.trans hw.symm
        have hal' : Arm.CheckSPAlignment P :=
          align_of_spEq (sw_r_eq hPw (f := .GPR 31#5) (by simp [Masked])).symm hal
        have herr' : Arm.r .ERR P = .None := by
          rw [← sw_r_eq hPw (f := .ERR) (by simp [Masked])]; exact herr
        have hU : placeUses ops (canonRegs ops) (useVals ops (canonRegs ops) P) w =
            placeUses ops (canonRegs ops) us w := by
          rw [useVals_eq, placeUses_eq, placeUses_eq]
          exact foldl_setReg_reads R us w' w hnd hplain hRl
        have hsem : csem Z ctx X i (useVals ops (canonRegs ops) P) w =
            some (defVals ops (canonRegs ops) t', t', .next) := by
          rw [csem_of_wf hctl (by simp [csemWF, hfo, hops, useVals_length ops _ hsz]) herr hal]
          simp only [straightSem, hops, hic, hU, hex]
          rw [if_pos (hA _ _), if_pos hok]
        obtain ⟨s', hs', hW, -, hD, -⟩ := (formOk_sound (F := Z) (X := X) hfo).1 env0 checkCtx0 ""
          ops (canonRegs ops) ic P w _ t' hops hcs hic hPw hal' herr' hsem
        have hdv : defVals ops (canonRegs ops) s' = defVals ops (canonRegs ops) t' := by
          unfold defVals
          refine map_eq_of_zip _ _ ?_ fun p hp => hD p hp
          simp [defVals]
        refine ⟨s', ?_, hW.symm⟩
        have hs'' : execMInst ctx env0 ic (placeUses ops (canonRegs ops) us w') = some s' := hs'
        simp only [straightSem, hops, hic]
        rw [if_pos (hA _ _)]
        simp only [hs'']
        have herrs : Arm.r .ERR s' = .None := by
          rw [sw_r_eq hW.symm (f := .ERR) (by simp [Masked])]; exact hok.1
        have hprog : s'.program = w'.program := by
          rw [hW.2.2, hok.2, hw.2.2]
        rw [if_pos ⟨herrs, hprog⟩, hdv]
      · cases h
    · cases h
  · cases h


/-! ## The memory-access forms -/

theorem SameWorld.mono {F Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {s t : Arm.ArmState}
    (h : SameWorld F s t) : SameWorld Z s t :=
  ⟨h.1, fun a ha => h.2.1 a (fun hf => ha (hFZ a hf)), h.2.2⟩

theorem amodeAddr_sameWorld {Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (sb : Nat) (am : AMode) (n : Nat) (us : List CV) :
    amodeAddr sb am n us w = amodeAddr sb am n us w' := by
  have hsp : spOf w = spOf w' := hw.1 (.GPR 31#5) (by simp [Masked])
  have h29 : Arm.r (.GPR 29#5) w = Arm.r (.GPR 29#5) w' := hw.1 (.GPR 29#5) (by simp [Masked])
  unfold amodeAddr
  split <;> simp only [hsp, h29]

theorem csem_load (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (op : LoadOp)
    (hop : op ≠ .fpuLoad128) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (us : List CV)
    (w : Arm.ArmState) (a : BitVec 64) (ha : amodeAddr ctx.slotBase am op.bytes us w = some a)
    (hav : Avoids F op.bytes a) :
    ∃ w', csem F ctx X (.load op (.vreg d .int) am fl) us w =
      some ([ofX (loadVal op a w)], w', .next) ∧ SameWorld F w' w := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_load F ctx op hop d am fl us w a ha hav hc.2.1 hc.2.2
  · exact ⟨w, by simp [mspec, hop, ha], SameWorld.refl F w⟩

theorem csem_store (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (op : StoreOp)
    (hop : op ≠ .fpuStore128) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (v : CV) (us : List CV)
    (w : Arm.ArmState) (a : BitVec 64) (ha : amodeAddr ctx.slotBase am op.bytes us w = some a)
    (hav : Avoids F op.bytes a) :
    ∃ w', csem F ctx X (.store op (.vreg d .int) am fl) (v :: us) w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes op.bytes a ((lo64 v).setWidth (op.bytes * 8)) w) := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_store F ctx op hop d am fl v us w a ha hav hc.2.1 hc.2.2
  · exact ⟨_, by simp [mspec, hop, ha], SameWorld.refl F _⟩

theorem csem_loadAcquire (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (ty : CTy)
    (hty : AtomTy ty) (d r : Nat) (fl : Clif.MemFlags) (u : CV) (w : Arm.ArmState)
    (hav : Avoids F ty.bytes (lo64 u)) :
    ∃ w', csem F ctx X (.loadAcquire ty (.vreg d .int) (.vreg r .int) fl) [u] w =
      some ([ofX ((Arm.read_mem_bytes ty.bytes (lo64 u) w).setWidth 64)], w', .next) ∧
      SameWorld F w' w := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_loadAcquire F ctx ty hty d r fl u w hav hc.2.1
  · exact ⟨w, by simp [mspec, hty], SameWorld.refl F w⟩

theorem csem_storeRelease (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (ty : CTy)
    (hty : AtomTy ty) (d r : Nat) (fl : Clif.MemFlags) (u v : CV) (w : Arm.ArmState)
    (hav : Avoids F ty.bytes (lo64 u)) :
    ∃ w', csem F ctx X (.storeRelease ty (.vreg d .int) (.vreg r .int) fl) [u, v] w =
      some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes ty.bytes (lo64 u) ((lo64 v).setWidth (ty.bytes * 8)) w) := by
  rw [csem_straight rfl]
  split
  · rename_i hc
    exact straight_storeRelease F ctx ty hty d r fl u v w hav hc.2.1
  · exact ⟨_, by simp [mspec, hty], SameWorld.refl F _⟩

/-- The bytes `[a, a + n)`. -/
def InBytes (a : BitVec 64) (n : Nat) (b : BitVec 64) : Prop := ∃ k < n, b = a + BitVec.ofNat 64 k

theorem write_bytes_eq_of {m1 m2 : Arm.Memory} :
    ∀ (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) (b : BitVec 64),
      (m1 b = m2 b ∨ InBytes a n b) →
      Arm.Memory.write_bytes n a v m1 b = Arm.Memory.write_bytes n a v m2 b
  | 0, _, _, b, h => by
    rcases h with h | ⟨k, hk, -⟩
    · exact h
    · omega
  | n + 1, a, v, b, h => by
    unfold Arm.Memory.write_bytes
    simp only
    apply write_bytes_eq_of (m1 := Arm.Memory.write a _ m1) (m2 := Arm.Memory.write a _ m2) n
    simp only [Arm.Memory.write, Arm.write_store]
    by_cases hb : b = a
    · left; simp [hb]
    · rcases h with h | ⟨k, hk, rfl⟩
      · left; simp [hb, h]
      · cases k with
        | zero => exact absurd (by simp) hb
        | succ j =>
          right
          refine ⟨j, by omega, ?_⟩
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, Nat.add_comm]

/-- Equal writes on two worlds that agree outside `Z`: they agree outside `Z` minus the written
bytes. -/
theorem SameWorld.write_both {Z : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld Z s t)
    (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) :
    SameWorld (fun b => Z b ∧ ¬ InBytes a n b) (Arm.write_mem_bytes n a v s)
      (Arm.write_mem_bytes n a v t) := by
  refine ⟨fun f hf => ?_, fun b hb => ?_, ?_⟩
  · rw [Arm.r_of_write_mem_bytes, Arm.r_of_write_mem_bytes]; exact h.1 f hf
  · rw [Arm.Memory.write_mem_bytes_eq_mem_write_bytes, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
    apply write_bytes_eq_of
    by_cases hz : Z b
    · exact .inr (Classical.byContradiction fun hn => hb ⟨hz, hn⟩)
    · exact .inl (h.2.1 b hz)
  · rw [Arm.write_mem_bytes_program, Arm.write_mem_bytes_program]; exact h.2.2


/-! ## One instruction -/

/-- What the lockstep of one instruction assumes of its memory accesses: a read (load, `ldar`)
avoids `Z` (the bytes where the two worlds may differ) and the frame `F`, a write avoids `F`, in
the forms the memory rules use. The LL/SC loops, `try_call` and `Args` are outside it. -/
def LockGuard (F Z : BitVec 64 → Prop) (sb : Nat) : MInst → List CV → Arm.ArmState → Prop
  | .load op (.vreg _ .int) am _, us, w => op ≠ .fpuLoad128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a ∧ Avoids Z op.bytes a
  | .store op (.vreg _ .int) am _, _ :: us, w => op ≠ .fpuStore128 ∧
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ Avoids F op.bytes a
  | .loadAcquire ty (.vreg _ .int) (.vreg _ .int) _, [u], _ =>
      AtomTy ty ∧ Avoids F ty.bytes (lo64 u) ∧ Avoids Z ty.bytes (lo64 u)
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _, [u, _], _ => AtomTy ty ∧ Avoids F ty.bytes (lo64 u)
  | .load .., _, _ | .store .., _, _ | .loadAcquire .., _, _ | .storeRelease .., _, _ => False
  | .atomicRmwLoop .., _, _ | .atomicCasLoop .., _, _ | .tryCall .., _, _ | .args _, _, _ => False
  | _, _, _ => True

/-- The bytes an instruction writes (the stores). -/
def WriteSet (sb : Nat) : MInst → List CV → Arm.ArmState → BitVec 64 → Prop
  | .store op (.vreg _ .int) am _, _ :: us, w => fun b =>
      ∃ a, amodeAddr sb am op.bytes us w = some a ∧ InBytes a op.bytes b
  | .storeRelease ty (.vreg _ .int) (.vreg _ .int) _, [u, _], _ => InBytes (lo64 u) ty.bytes
  | _, _, _ => fun _ => False

theorem writeSet_nil {sb : Nat} {i : MInst} (h : i.isMemAcc = false) (us : List CV)
    (w : Arm.ArmState) (b : BitVec 64) : ¬ WriteSet sb i us w b := by
  cases i <;> simp_all [WriteSet, MInst.isMemAcc]

theorem CondBrKind.holds_sameWorld {Z : BitVec 64 → Prop} {w w' : Arm.ArmState}
    (hw : SameWorld Z w w') (k : CondBrKind) (us : List CV) : k.holds us w = k.holds us w' := by
  unfold CondBrKind.holds
  split <;> simp [ConditionHolds_sameWorld hw]

theorem sameWorld_minus {Z W : BitVec 64 → Prop} (hW : ∀ b, ¬ W b) {s t : Arm.ArmState}
    (h : SameWorld Z s t) : SameWorld (fun b => Z b ∧ ¬ W b) s t :=
  ⟨h.1, fun b hb => h.2.1 b (fun hz => hb ⟨hz, hW b⟩), h.2.2⟩

theorem minus_of_frame {F Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {n : Nat} {a : BitVec 64}
    (hav : Avoids F n a) : ∀ b, F b → Z b ∧ ¬ InBytes a n b := fun b hb =>
  ⟨hFZ b hb, fun ⟨k, hk, e⟩ => hav k hk (e ▸ hb)⟩

set_option maxHeartbeats 4000000 in
/-- The specification fallback of `csem` on a form without memory access. -/
theorem mspec_lockstep {Z : BitVec 64 → Prop} {sb : Nat} {i : MInst} (hm : i.isMemAcc = false)
    {us : List CV} {w w' : Arm.ArmState} (hw : SameWorld Z w w') {o : List CV} {w₁ : Arm.ArmState}
    {c : Ctl} (h : mspec sb i us w = some (o, w₁, c)) :
    ∃ w₁', mspec sb i us w' = some (o, w₁', c) ∧ SameWorld Z w₁ w₁' := by
  have hsp : spOf w = spOf w' := hw.1 (.GPR 31#5) (by simp [Masked])
  unfold mspec at h ⊢
  split at h
  · simp [MInst.isMemAcc] at hm
  · simp [MInst.isMemAcc] at hm
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨w', by rw [hsp], hw⟩
  · simp [MInst.isMemAcc] at hm
  · simp [MInst.isMemAcc] at hm
  · obtain ⟨w₁', h1, h2⟩ := ispec_lockstep hw h
    exact ⟨w₁', h1, h2⟩

set_option maxHeartbeats 4000000 in
/-- **The lockstep of `csem` on one instruction**: two worlds that agree outside `Z` (containing
the frame `F`), an instruction whose reads avoid `Z` (`LockGuard`), callees (of a `call`) and the
TLSDESC resolver that keep the agreement (`hX`, `hT`): the same outputs and control, worlds that
agree outside `Z` minus the bytes written. -/
theorem csem_lockstep {F Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us : List CV} {w w' : Arm.ArmState} (hw : SameWorld Z w w')
    (hg : LockGuard F Z ctx.slotBase i us w)
    (hX : ∀ info, i = .call info → ∀ d o x, X.call d us w = some (o, x) →
      ∃ x', X.call d us w' = some (o, x') ∧ SameWorld Z x x')
    (hT : ∀ n, X.tlsFlags n w = X.tlsFlags n w')
    {o : List CV} {w₁ : Arm.ArmState} {c : Ctl} (h : csem F ctx X i us w = some (o, w₁, c)) :
    ∃ w₁', csem F ctx X i us w' = some (o, w₁', c) ∧
      SameWorld (fun b => Z b ∧ ¬ WriteSet ctx.slotBase i us w b) w₁ w₁' := by
  have herr : Arm.r .ERR w = Arm.r .ERR w' := hw.1 .ERR (by simp [Masked])
  have hsp : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) w' := hw.1 (.GPR 31#5) (by simp [Masked])
  cases hmem : i.isMemAcc
  · -- no memory access
    suffices hs : ∃ w₁', csem F ctx X i us w' = some (o, w₁', c) ∧ SameWorld Z w₁ w₁' by
      obtain ⟨w₁', h1, h2⟩ := hs
      exact ⟨w₁', h1, sameWorld_minus (writeSet_nil hmem us w) h2⟩
    unfold csem at h ⊢
    split at h
    · -- call
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨o', x⟩, hp, rfl, rfl, rfl⟩ := h
      obtain ⟨x', hx', hs⟩ := hX _ (by first | rfl | assumption) _ _ _ hp
      exact ⟨x', by rw [hx']; rfl, hs⟩
    · simp [LockGuard] at hg
    · simp [LockGuard] at hg
    all_goals (try simp only [CondBrKind.holds_sameWorld hw, ConditionHolds_sameWorld hw, hT] at h)
    all_goals first
      | (simp [LockGuard] at hg; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         first
         | exact ⟨w', rfl, hw⟩
         | exact ⟨_, rfl, SameWorld.write_pstate' hw _⟩)
      | skip
    case h_17 =>
      have hctl : i.isCtl = false := by
        cases i <;> simp [MInst.isCtl] <;> (exfalso; solve_by_elim)
      by_cases hc : csemWF ctx i us = true ∧ Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w
      · rw [if_pos hc] at h
        have hc' : csemWF ctx i us = true ∧ Arm.r .ERR w' = .None ∧ Arm.CheckSPAlignment w' :=
          ⟨hc.1, herr ▸ hc.2.1, align_of_spEq hsp.symm hc.2.2⟩
        rw [if_pos hc']
        have hfo : FormOk ctx i = true := by
          have := hc.1; simp only [csemWF, Bool.and_eq_true] at this; exact this.1
        exact straight_lockstep X hfo hmem hctl hc.1 hw hc.2.1 hc.2.2 h
      · rw [if_neg hc] at h
        have hc' : ¬ (csemWF ctx i us = true ∧ Arm.r .ERR w' = .None ∧ Arm.CheckSPAlignment w') :=
          fun h' => hc ⟨h'.1, herr ▸ h'.2.1, align_of_spEq hsp h'.2.2⟩
        rw [if_neg hc']
        exact mspec_lockstep hmem hw h
    all_goals (
      split at h
      all_goals (try (split at h))
      all_goals (try (split at h))
      all_goals (try (cases h; done))
      all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h)
      all_goals (refine ⟨w', ?_, hw⟩; simp_all))
  · -- the memory forms
    unfold LockGuard at hg
    split at hg
    · rename_i op d am fl
      obtain ⟨hop, a, ha, hF, hZ⟩ := hg
      obtain ⟨w₂, h2, hs2⟩ := csem_load F ctx X op hop d am fl us w a ha hF
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨w₂', h2', hs2'⟩ := csem_load F ctx X op hop d am fl us w' a
        (by rw [← amodeAddr_sameWorld hw]; exact ha) hF
      have hlv : loadVal op a w = loadVal op a w' := by
        unfold loadVal; rw [read_mem_bytes_sameWorld hw hZ]
      refine ⟨w₂', by rw [h2', hlv], sameWorld_minus (fun b hb => by simp [WriteSet] at hb) ?_⟩
      exact SameWorld.trans (SameWorld.mono hFZ hs2) (hw.trans (SameWorld.mono hFZ hs2').symm)
    · rename_i op d am fl v us
      obtain ⟨hop, a, ha, hF⟩ := hg
      obtain ⟨w₂, h2, hs2⟩ := csem_store F ctx X op hop d am fl v us w a ha hF
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨w₂', h2', hs2'⟩ := csem_store F ctx X op hop d am fl v us w' a
        (by rw [← amodeAddr_sameWorld hw]; exact ha) hF
      refine ⟨w₂', h2', ?_⟩
      have hm := minus_of_frame hFZ hF
      have e : (fun b => Z b ∧ ¬ WriteSet ctx.slotBase (.store op (.vreg d .int) am fl) (v :: us) w b) =
          fun b => Z b ∧ ¬ InBytes a op.bytes b := by
        funext b; simp only [WriteSet, ha, Option.some.injEq, exists_eq_left']
      rw [e]
      exact SameWorld.trans (SameWorld.mono hm hs2) ((SameWorld.write_both hw _ _ _).trans (SameWorld.mono hm hs2').symm)
    · rename_i ty d r fl u
      obtain ⟨hty, hF, hZ⟩ := hg
      obtain ⟨w₂, h2, hs2⟩ := csem_loadAcquire F ctx X ty hty d r fl u w hF
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨w₂', h2', hs2'⟩ := csem_loadAcquire F ctx X ty hty d r fl u w' hF
      refine ⟨w₂', by rw [h2', read_mem_bytes_sameWorld hw hZ],
        sameWorld_minus (fun b hb => by simp [WriteSet] at hb) ?_⟩
      exact SameWorld.trans (SameWorld.mono hFZ hs2) (hw.trans (SameWorld.mono hFZ hs2').symm)
    · rename_i ty d r fl u v
      obtain ⟨hty, hF⟩ := hg
      obtain ⟨w₂, h2, hs2⟩ := csem_storeRelease F ctx X ty hty d r fl u v w hF
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨w₂', h2', hs2'⟩ := csem_storeRelease F ctx X ty hty d r fl u v w' hF
      refine ⟨w₂', h2', ?_⟩
      have hm := minus_of_frame hFZ hF
      exact SameWorld.trans (SameWorld.mono hm hs2) ((SameWorld.write_both hw _ _ _).trans (SameWorld.mono hm hs2').symm)
    all_goals first
      | exact hg.elim
      | (exfalso; cases i <;> simp [MInst.isMemAcc] at hmem <;> solve_by_elim)

/-! ## The LL/SC loops, on two runs -/

theorem loopSem_inv' {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {c : Ctl} (h : loopSem F ty a body regs uses defs w = some (outs, w', c)) :
    AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧
      execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) = some w' ∧
      outs = (defs.take 1).map (regVal w') ++ (defs.drop 1).map (fun _ => ofX 0) ∧ c = .next := by
  unfold loopSem at h
  split at h
  · rename_i hc
    split at h
    · rename_i t' ht
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hc.1, hc.2.1, ht, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem regVal_x_eq {s t : Arm.ArmState} {n : Nat} (h : Arm.r (.GPR (rnum n)) s = Arm.r (.GPR (rnum n)) t) :
    regVal s (.x n) = regVal t (.x n) := by
  simp only [regVal, h]

theorem SameWorld.write_both_mono {Z : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld Z s t)
    (n : Nat) (a : BitVec 64) (v : BitVec (n * 8)) :
    SameWorld Z (Arm.write_mem_bytes n a v s) (Arm.write_mem_bytes n a v t) :=
  SameWorld.mono (fun _ hb => hb.1) (SameWorld.write_both h n a v)

set_option maxHeartbeats 4000000 in
/-- **The `atomic_rmw` loop on two runs**: two worlds that agree outside `Z`, an access avoiding
`Z`: the same outputs (the old value; the scratch defs are 0) and worlds that agree outside
`Z`. -/
theorem rmw_lockstep2 {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {ty : CTy}
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {a b c d e : Reg} {u x : CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w') (hZ : Avoids Z ty.bytes (lo64 u))
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {k k' : Ctl}
    (h : csem F ctx X (.atomicRmwLoop ty op fl a b c d e) [u, x] w = some (o, w₁, k))
    (h' : csem F ctx X (.atomicRmwLoop ty op fl a b c d e) [u, x] w' = some (o', w₁', k')) :
    o = o' ∧ k = k' ∧ SameWorld Z w₁ w₁' := by
  have herr : Arm.r .ERR w = Arm.r .ERR w' := hw.1 .ERR (by simp [Masked])
  simp only [csem] at h h'
  by_cases he : Arm.r .ERR w = .None
  · rw [if_pos he] at h
    rw [if_pos (herr ▸ he)] at h'
    obtain ⟨hty, -, hrun, rfl, rfl⟩ := loopSem_inv' h
    obtain ⟨-, -, hrun', rfl, rfl⟩ := loopSem_inv' h'
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
      rnum] at hrun hrun'
    have hsw0 : SameWorld Z (Arm.w (.GPR 26#5) (lo64 x) (Arm.w (.GPR 25#5) (lo64 u) w))
        (Arm.w (.GPR 26#5) (lo64 x) (Arm.w (.GPR 25#5) (lo64 u) w')) :=
      SameWorld.w_both (SameWorld.w_both hw)
    have hav : Avoids Z ty.bytes (Arm.r (.GPR 25#5)
        (Arm.w (.GPR 26#5) (lo64 x) (Arm.w (.GPR 25#5) (lo64 u) w'))) := by
      rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]; exact hZ
    obtain ⟨hsw, h27⟩ := rmwBody_congr (F := Z) hty op fl env0 env0 hsw0
      (by simp [Arm.r_of_w_different]) (by simp [Arm.r_of_w_different]) hav hrun hrun'
    refine ⟨?_, rfl, hsw⟩
    simp only [List.take, List.drop, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.cons.injEq, and_true]
    exact regVal_x_eq (by simpa [rnum] using h27)
  · rw [if_neg he] at h
    rw [if_neg (herr ▸ he)] at h'
    split at h
    · rw [if_pos ‹_›] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h h'
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [read_mem_bytes_sameWorld hw hZ]
      exact ⟨rfl, rfl, SameWorld.write_both_mono hw _ _ _⟩
    · cases h

set_option maxHeartbeats 4000000 in
/-- **The `atomic_cas` loop on two runs** (as `rmw_lockstep2`). -/
theorem cas_lockstep2 {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {ty : CTy}
    {fl : Clif.MemFlags} {a b c d e : Reg} {u v x : CV}
    {w w' : Arm.ArmState} (hw : SameWorld Z w w') (hZ : Avoids Z ty.bytes (lo64 u))
    {o o' : List CV} {w₁ w₁' : Arm.ArmState} {k k' : Ctl}
    (h : csem F ctx X (.atomicCasLoop ty fl a b c d e) [u, v, x] w = some (o, w₁, k))
    (h' : csem F ctx X (.atomicCasLoop ty fl a b c d e) [u, v, x] w' = some (o', w₁', k')) :
    o = o' ∧ k = k' ∧ SameWorld Z w₁ w₁' := by
  have herr : Arm.r .ERR w = Arm.r .ERR w' := hw.1 .ERR (by simp [Masked])
  simp only [csem] at h h'
  by_cases he : Arm.r .ERR w = .None
  · rw [if_pos he] at h
    rw [if_pos (herr ▸ he)] at h'
    split at h
    · rename_i outs t1 c1 hhead
      split at h'
      · rename_i outs' t1' c1' hhead'
        obtain ⟨hty, -, hrun, rfl, rfl⟩ := loopSem_inv' hhead
        obtain ⟨-, -, hrun', rfl, rfl⟩ := loopSem_inv' hhead'
        simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
          setReg_x, rnum] at hrun hrun'
        have hsw0 : SameWorld Z (Arm.w (.GPR 28#5) (lo64 x) (Arm.w (.GPR 26#5) (lo64 v)
            (Arm.w (.GPR 25#5) (lo64 u) w))) (Arm.w (.GPR 28#5) (lo64 x) (Arm.w (.GPR 26#5) (lo64 v)
            (Arm.w (.GPR 25#5) (lo64 u) w'))) :=
          SameWorld.w_both (SameWorld.w_both (SameWorld.w_both hw))
        have hav : Avoids Z ty.bytes (Arm.r (.GPR 25#5) (Arm.w (.GPR 28#5) (lo64 x)
            (Arm.w (.GPR 26#5) (lo64 v) (Arm.w (.GPR 25#5) (lo64 u) w')))) := by
          simp only [Arm.r_of_w_different (show Arm.StateField.GPR 25#5 ≠ .GPR 28#5 by decide),
            Arm.r_of_w_different (show Arm.StateField.GPR 25#5 ≠ .GPR 26#5 by decide),
            Arm.r_of_w_same]; exact hZ
        obtain ⟨hsw1, h27⟩ := casHead_congr (F := Z) hty fl env0 env0 hsw0
          (by simp [Arm.r_of_w_different]) (by simp [Arm.r_of_w_different]) hav hrun hrun'
        have hcond : Arm.ConditionHolds Cond.ne.bits t1 = Arm.ConditionHolds Cond.ne.bits t1' :=
          ConditionHolds_sameWorld hsw1 _
        by_cases hc : Arm.ConditionHolds Cond.ne.bits t1 = true
        · rw [if_pos hc] at h
          rw [if_pos (hcond ▸ hc)] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h h'
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := h'
          refine ⟨?_, rfl, hsw1⟩
          simp only [List.take, List.drop, List.map_cons, List.map_nil, List.cons_append,
            List.nil_append, List.cons.injEq, and_true]
          exact regVal_x_eq (by simpa [rnum] using h27)
        · rw [if_neg hc] at h
          rw [if_neg (hcond ▸ hc)] at h'
          obtain ⟨-, -, hrun2, rfl, rfl⟩ := loopSem_inv' h
          obtain ⟨-, -, hrun2', rfl, rfl⟩ := loopSem_inv' h'
          simp only [List.zip_nil_left, List.foldl_nil] at hrun2 hrun2'
          obtain ⟨t0, ht0, -, -, hfr0, -, -, -⟩ := casHead_spec hty fl env0 _
            (by simp [Arm.r_of_w_different, he] : Arm.r .ERR (Arm.w (.GPR 28#5) (lo64 x)
              (Arm.w (.GPR 26#5) (lo64 v) (Arm.w (.GPR 25#5) (lo64 u) w))) = .None)
          rw [hrun, Option.some.injEq] at ht0
          subst ht0
          obtain ⟨t0', ht0', -, -, hfr0', -, -, -⟩ := casHead_spec hty fl env0 _
            (by simp [Arm.r_of_w_different, ← herr, he] : Arm.r .ERR (Arm.w (.GPR 28#5) (lo64 x)
              (Arm.w (.GPR 26#5) (lo64 v) (Arm.w (.GPR 25#5) (lo64 u) w'))) = .None)
          rw [hrun', Option.some.injEq] at ht0'
          subst ht0'
          have herrt : Arm.r .ERR t1 = .None := by
            rw [hfr0 .ERR (by simp) (by simp) (by simp)]; simp [Arm.r_of_w_different, he]
          have h25 : Arm.r (.GPR 25#5) t1 = Arm.r (.GPR 25#5) t1' := by
            rw [hfr0 _ (by simp) (by simp) (by simp), hfr0' _ (by simp) (by simp) (by simp)]
            simp [Arm.r_of_w_different]
          have h28 : Arm.r (.GPR 28#5) t1 = Arm.r (.GPR 28#5) t1' := by
            rw [hfr0 _ (by simp) (by simp) (by simp), hfr0' _ (by simp) (by simp) (by simp)]
            simp [Arm.r_of_w_different]
          have hsw2 := stlxr_congr (F := Z) hty fl env0 env0 hsw1 h25 h28 hrun2 hrun2'
          obtain ⟨s2, hs2, -, hfrs, -, -⟩ := stlxr_spec hty fl env0 t1 herrt
          rw [hrun2, Option.some.injEq] at hs2
          subst hs2
          have herrt' : Arm.r .ERR t1' = .None := by
            rw [← hsw1.1 .ERR (by simp [Masked])]; exact herrt
          obtain ⟨s2', hs2', -, hfrs', -, -⟩ := stlxr_spec hty fl env0 t1' herrt'
          rw [hrun2', Option.some.injEq] at hs2'
          subst hs2'
          refine ⟨?_, rfl, hsw2⟩
          simp only [List.take, List.drop, List.map_cons, List.map_nil, List.cons_append,
            List.nil_append, List.cons.injEq, and_true]
          refine regVal_x_eq ?_
          simp only [rnum]
          rw [hfrs _ (by simp) (by simp), hfrs' _ (by simp) (by simp)]
          simpa [rnum] using h27
      · cases h'
    · cases h
  · rw [if_neg he] at h
    rw [if_neg (herr ▸ he)] at h'
    split at h
    · rw [if_pos ‹_›] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h h'
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := h'
      rw [read_mem_bytes_sameWorld hw hZ]
      refine ⟨rfl, rfl, ?_⟩
      split
      · exact SameWorld.write_both_mono hw _ _ _
      · exact hw
    · cases h

end E2E
