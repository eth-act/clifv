import FV.E2E.DeadCleanupStackBound
import FV.E2E.StackBoundT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT

/-! # Typed copies of `FV.E2E.DeadCleanupStackBound` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupStackBound` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefinesT`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupStackBound
set_option autoImplicit false
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound

/-- **`backend_correct_program_stack` for the function named `n`** of the linked system `L` of
the input `I`, every premise but `L.OkT`: for every fuel `M`, from an entry whose `sp` has
`stackFn I f` bytes below it (without wrapping) holding no code of the program, with the
addresses outside the world that stack and the code. -/
def ProgStmtST (L : LinkSys) (I : LinkInput) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s →
    stackFn I f ≤ (spv s).toNat → (∀ a, L.Img a → ¬ StackBelow (stackFn I f) (spv s) a) →
    L.F = frameWG (bud I f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

/-- **The crate's theorem with the stack bound** for its function named `n` (`CrateStmt` with
`ProgStmtST`). -/
def StackStmtT (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputCleanup I B F) →
    (∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) → ProgStmtST (LinkSys.ofInputCleanup I B F) I n

/-- **A function whose calls never reach a call cycle** (`goodN`) of an input that passes the
checker refines at every fuel with its stack bound `stackFn I f`. -/
theorem crate_correct_stackNT {I : LinkInput} (hI : okBCleanup I = true) {n : String}
    (hn : goodN I n = true) : StackStmtT I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  refine backend_correct_program_stackT _ (okBCleanup_soundT hI hB hFI) (budget_ofT hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
end E2E.DeadCleanupStackBound
