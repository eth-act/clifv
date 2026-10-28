import FV.E2E.LinkArmX30Check
import FV.E2E.LinkArmStepFrameRec
import FV.E2E.LinkGood

/-!
# One step of the `x30` lock-step per line kind (SEM1, `docs/plans/uninit.md` §5.9, step 3o)

The single steps of the lock-step of prophecy determinism (`StEqOutX`, equal but for `x30` and
bytes in `Z`), on the activation's machine `ArmStepX X H fa` at an instruction line of the
laid-out function (`OnLine`: the second state `t`, the canonical one, holds the program and has
no error; its pc is at line `j` with instruction `x`):

* `stEqOutX_line_free`: a line the `x30` check covers (`x.x30Exempt = false`, `FnAsm.x30Free`):
  its reads avoid `Z` (and a TLS hook keeps `StEqOutX Z`) ⇒ `StEqOutX Z`;
* `stEqOutX_line_call`: `bl`/`blr` ⇒ whatever the call hook gives;
* `stEqOutX_line_stpFR`: the prologue's `stp fp, lr, [sp, #-16]!` adds the record's saved-LR
  bytes to `Z`;
* `stEqOutX_line_ldpFR`: the epilogue's `ldp fp, lr, [sp], #16` keeps `StEqOutX Z` when the
  saved `fp` is outside `Z`;
* `retAgree_line_ret`: `ret` gives states equal on every register but `x30` and the pc and on the
  memory outside `Z`;
* `lockstep_runX`: the run induction from per-index steps.
-/

namespace E2E

open Arm Backend Backend.Proof Concurrency.ArmFoot Concurrency.ArmThread GprFoot

/-- **`t` is at instruction line `x`** of the laid-out function `fa` (`fb`, labels `lm`, loaded
at `base`), with no error. -/
structure OnLine (fa : FnAsm) (fb : FnBin) (lm : Std.HashMap Lbl Nat) (base : BitVec 64)
    (t : ArmState) (x : Insn) : Prop where
  layout : fa.layout = .ok fb
  lm : labelOffsets fa.lines = .ok lm
  fit : 4 * fb.words.size ≤ 2 ^ 64
  prog : t.program = fb.program base
  err : r .ERR t = .None
  line : ∃ j tc, fa.lines.toList[j]? = some (.ins x tc) ∧
    r .PC t = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)

namespace OnLine

variable {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
  {t : ArmState} {x : Insn}

theorem insnAt_eq (h : OnLine fa fb lm base t x) :
    Backend.Proof.insnAt fa (progBase t) (r .PC t) = some x := by
  obtain ⟨j, tc, hj, hpc⟩ := h.line
  rw [hpc]; exact LinkSys.insnAt_ofLine h.layout h.lm h.fit h.prog hj

theorem decodeAt (h : OnLine fa fb lm base t x) :
    ∃ j a, x.toArmInst ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = .ok a ∧ decodeAt t = some a := by
  obtain ⟨j, tc, hj, hpc⟩ := h.line
  obtain ⟨a, ha, hd⟩ := decodeAt_ofLine h.layout h.lm h.fit h.prog hj hpc
  exact ⟨j, a, ha, hd⟩

end OnLine

theorem insnAt_congrX {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) (fa : FnAsm) :
    insnAt fa (progBase s) (r .PC s) = insnAt fa (progBase t) (r .PC t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  rw [hpb, h.1 .PC (by simp)]

theorem decodeAt_congrX {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) :
    Concurrency.ArmFoot.decodeAt s = Concurrency.ArmFoot.decodeAt t := by
  simp only [Concurrency.ArmFoot.decodeAt, fetch_inst, h.2.1, h.1 .PC (by simp)]

/-- **A line the `x30` check covers.** -/
theorem stEqOutX_line_free {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hc : fa.x30Free lm = true)
    (hx : x.x30Exempt = false) (h : StEqOutX Z s t) (hZ : E2E.ReadsAvoid Z (stepiEvs t))
    (htls : ∀ n r', (∃ a b c, x = .ldrTlsDescLo12 a b c) → StEqOutX Z (H.tls n r' s) (H.tls n r' t)) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  obtain ⟨j, tc, hj, hpc⟩ := ht.line
  have h30 := decX30Free_of_line ht.layout ht.lm ht.fit hc ht.prog hj hx hpc
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc' : r .PC s = r .PC t := h.1 .PC (by simp)
  simp only [ArmStepX, hpb, hpc', ht.insnAt_eq]
  split
  all_goals first
    | (rename_i hh; exact htls _ _ ⟨_, _, _, Option.some.inj hh⟩)
    | exact stEqOutX_w (stEqOutX_w h _ _) _ _
    | exact stEqOutX_w h _ _
    | exact stEqOutX_stepi h hZ h30
    | (exfalso; rename_i hh; simp only [Option.some.injEq] at hh; subst hh
       simp [Insn.x30Exempt] at hx; done)

/-- **A call line** (`bl`, `blr`): the hook's states. -/
theorem stEqOutX_line_call {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z Z' : BitVec 64 → Prop} {s t : ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hb : (∃ n, x = .bl n) ∨ ∃ r', x = .blr r')
    (h : StEqOutX Z s t) (hcall : ∀ d, StEqOutX Z' (H.call d s) (H.call d t)) :
    StEqOutX Z' (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc' : r .PC s = r .PC t := h.1 .PC (by simp)
  have hi := ht.insnAt_eq
  rcases hb with ⟨n, rfl⟩ | ⟨r', rfl⟩ <;> simp only [ArmStepX, hpb, hpc', hi] <;> exact hcall _

/-- `ArmStepX` at a line it hands to `stepi`, on two `StEqOutX` states: both execute the
decoded instruction. -/
theorem armStepX_exec_pair {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    {x : Insn} {a : ArmInst} (ht : OnLine fa fb lm base t x) (h : StEqOutX Z s t)
    (hst : ∀ u, Backend.Proof.insnAt fa (progBase u) (r .PC u) = some x →
      ArmStepX X H fa u = stepi u)
    (ha : ∀ env, x.toArmInst env = .ok a) :
    ArmStepX X H fa s = exec_inst a s ∧ ArmStepX X H fa t = exec_inst a t := by
  obtain ⟨j, a', ha', hd⟩ := ht.decodeAt
  rw [ha] at ha'; cases ha'
  have hi := ht.insnAt_eq
  have herr : r .ERR s = r .ERR t := h.1 .ERR (by simp)
  refine ⟨?_, ?_⟩
  · rw [hst s ((insnAt_congrX h fa).trans hi)]
    exact stepi_of_decodeAt (herr.trans ht.err) ((decodeAt_congrX h).trans hd)
  · rw [hst t hi]; exact stepi_of_decodeAt ht.err hd

/-- **The prologue's frame-record store** adds the record's saved-LR bytes to `Z`. -/
theorem stEqOutX_line_stpFR {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    (ht : OnLine fa fb lm base t (.stp .fp .lr (.spPreIndexed (-16)))) (h : StEqOutX Z s t) :
    StEqOutX (fun a => Z a ∨ HiBytes (stpAddr 0x7e t) 8 16 a) (ArmStepX X H fa s)
      (ArmStepX X H fa t) := by
  obtain ⟨hs, ht'⟩ := armStepX_exec_pair (a := stpFR 0x7e) (X := X) (H := H) ht h
    (fun u hu => by simp only [ArmStepX, hu]) (fun _ => rfl)
  rw [hs, ht']
  exact stEqOutX_stpFR 0x7e h

/-- **The epilogue's frame-record load** keeps `StEqOutX Z` when the saved `fp` (the 8 bytes at
`sp`) is outside `Z`. -/
theorem stEqOutX_line_ldpFR {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    (ht : OnLine fa fb lm base t (.ldp .fp .lr (.spPostIndexed 16))) (h : StEqOutX Z s t)
    (hlo : ∀ k < 8, ¬ Z (read_gpr 64 31 t + BitVec.ofNat 64 k)) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  obtain ⟨hs, ht'⟩ := armStepX_exec_pair (a := ldpFR 2) (X := X) (H := H) ht h
    (fun u hu => by simp only [ArmStepX, hu]) (fun _ => rfl)
  rw [hs, ht']
  exact stEqOutX_ldpFR 2 h hlo

/-- **`ret`**: the two states agree on every register but `x30` and the pc, on the program, and
on the memory outside `Z`. -/
theorem retAgree_line_ret {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    (ht : OnLine fa fb lm base t .ret) (h : StEqOutX Z s t) :
    (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → r f (ArmStepX X H fa s) = r f (ArmStepX X H fa t)) ∧
      (ArmStepX X H fa s).program = (ArmStepX X H fa t).program ∧
      ∀ a, ¬ Z a → (ArmStepX X H fa s).mem a = (ArmStepX X H fa t).mem a := by
  obtain ⟨hs, ht'⟩ := armStepX_exec_pair (a := retI) (X := X) (H := H) ht h
    (fun u hu => by simp only [ArmStepX, hu]) (fun _ => rfl)
  rw [hs, ht']
  exact stEqOutX_ret h

/-- The lock-step set after the step at line `x` from `t`: the prologue's record store adds the
record's saved-LR bytes. -/
def zNext (Z : BitVec 64 → Prop) (x : Insn) (t : ArmState) : BitVec 64 → Prop :=
  fun a => Z a ∨ (x = .stp .fp .lr (.spPreIndexed (-16)) ∧ HiBytes (stpAddr 0x7e t) 8 16 a)

/-- **One step of the lock-step at any instruction line but `ret` and the TLS tail.** The
obligations per line kind: a checked line reads nothing in `Z`; the epilogue's `ldp` reloads
`fp` from outside `Z`; a call / TLS hook keeps `StEqOutX Z`. -/
theorem stEqOutX_line {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hc : fa.x30Free lm = true)
    (htail : x.tlsTail = false) (hret : x ≠ .ret) (h : StEqOutX Z s t)
    (hZ : x.x30Exempt = false → E2E.ReadsAvoid Z (stepiEvs t))
    (hlo : x = .ldp .fp .lr (.spPostIndexed 16) →
      ∀ k < 8, ¬ Z (read_gpr 64 31 t + BitVec.ofNat 64 k))
    (hcall : ((∃ n, x = .bl n) ∨ ∃ r', x = .blr r') → ∀ d, StEqOutX Z (H.call d s) (H.call d t))
    (htls : ∀ n r', (∃ a b c, x = .ldrTlsDescLo12 a b c) → StEqOutX Z (H.tls n r' s) (H.tls n r' t)) :
    StEqOutX (zNext Z x t) (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hmono : ∀ a, Z a → zNext Z x t a := fun _ ha => .inl ha
  cases hE : x.x30Exempt with
  | false => exact (stEqOutX_line_free ht hc hE h (hZ hE) htls).mono hmono
  | true =>
    rcases x30Exempt_cases hE with ⟨n, rfl⟩ | ⟨r', rfl⟩ | ⟨r', n, rfl⟩ | rfl | rfl | rfl
    · exact stEqOutX_line_call ht (.inl ⟨n, rfl⟩) h fun d => (hcall (.inl ⟨n, rfl⟩) d).mono hmono
    · exact stEqOutX_line_call ht (.inr ⟨r', rfl⟩) h fun d => (hcall (.inr ⟨r', rfl⟩) d).mono hmono
    · simp [Insn.tlsTail] at htail
    · exact absurd rfl hret
    · exact (stEqOutX_line_stpFR ht h).mono fun a ha => ha.elim .inl fun hb => .inr ⟨rfl, hb⟩
    · exact (stEqOutX_line_ldpFR ht h (hlo rfl)).mono hmono

theorem runX_succ_app (f : ArmState → ArmState) (k : Nat) (s : ArmState) :
    runX f (k + 1) s = f (runX f k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (f s)

/-- **The run induction of the lock-step**: `StEqOutX (Zs i)` at every index up to `n`, from
the entries and one step per index. -/
theorem lockstep_runX {f : ArmState → ArmState} {Zs : Nat → BitVec 64 → Prop} {s t : ArmState}
    {n : Nat} (h0 : StEqOutX (Zs 0) s t)
    (hstep : ∀ i < n, StEqOutX (Zs i) (runX f i s) (runX f i t) →
      StEqOutX (Zs (i + 1)) (f (runX f i s)) (f (runX f i t))) :
    ∀ i ≤ n, StEqOutX (Zs i) (runX f i s) (runX f i t) := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih =>
    rw [runX_succ_app, runX_succ_app]
    exact hstep i (by omega) (ih (by omega))

end E2E
