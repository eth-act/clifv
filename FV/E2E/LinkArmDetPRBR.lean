import FV.E2E.LinkArmProgCallPRB

/-!
# Determinism of `ThmPRB`'s outcome for returning CLIF runs (SEM1 #537, #719)

Finding (#719): `DetPRB κ M` (`LinkArmProgCallPRB.lean`) asks the machine run from every entry
`s` agreeing with the canonical `s₀` to realise the canonical outcome **without** the canonical
activation's CLIF run returning. That is false for any `g` that loads through a pointer argument:
at a CLIF address that is not a valid (or not an initialised) byte `MemRel` relates nothing, so
the two body-entry worlds may differ there (`D`), the machine reads the byte and returns
different values, while CLIF is stuck. The backend two-run theorems (`backend_pairRunD`,
`backend_twoRunLERWZI`) need exactly the returning CLIF run. Every use site has it: `progCallPRB*`
applies `hdet` to the canonical callee activation right after `ThmPRB*` on the same returning
callee run.

Decision (conservative: new names, `DetPRB` kept): **`DetPRBR κ M`**, `DetPRB` with the
canonical activation's returning CLIF run (`Clif.runLoop (L.envR M g) L.P.bare fuel cs`, as
`ThmPRBRL`), its linked-call return address (`RaOk`), and for the agreeing entry its return
address and frame pointer (`x29`, which `EntryAgree` does not cover; at a call both are the
caller's). `DetPRB.toR` (every `DetPRB` is a `DetPRBR`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Determinism of `ThmPRB`'s outcome for returning CLIF runs** (module doc): `DetPRB` with
the canonical activation's CLIF run returning, both return addresses linked calls' (`RaOk`) and
the two entries' frame pointers equal. -/
def DetPRBR (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
    (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
    (n₀ e fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
    L.TableOf M g s₀ ini →
    ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
    PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
    L.TabUpTo M g s₀ ini.bytes ini.next n₀ e →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    RaOk (L.A g) (ra₀ - 4) →
    ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g (spv w₀) cs.frame.slots cs.mem w₀' →
      SameWorld (fun a => F a ∨ D a) w₀ w₀' →
      (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
        EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
        RaOk (L.A g) (ra - 4) →
        Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) s₀ →
        ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
          L.TabUpTo M g s ini.bytes ini.next n e

/-- **Every `DetPRB` is a `DetPRBR`** (the extra premises unused). -/
theorem DetPRB.toR {M : Nat} (h : L.DetPRB κ M) : L.DetPRBR κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e _ _ _ hWE hME₀ htab hret₀ hpt₀ htab₀ _ _ D
    w₀' hrel hsw hreg hstk G ra s hME hag _ _ =>
    h g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e hWE hME₀ htab hret₀ hpt₀ htab₀ D w₀' hrel hsw
      hreg hstk G ra s hME hag

end LinkSys

end E2E
