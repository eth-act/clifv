import FV.E2E.LinkArmProph
import FV.Backend.Proof.VCodeSemI

/-!
# The linking statement with the prophecy-indexed call contract (SEM1 step 2, `docs/plans/uninit.md` §5.4)

The counted VCode run of an activation of `g` (`csemI`) takes its call results from an
`ExtSemI`; with the refined call contract that is `XPI … P`, call number `n` the canonical callee
run from the VCode world with the callee's stack region holding `P n` (`LinkSys.XP`). `P n` is
the actual machine memory at the activation's `n`-th call, so it is a function of the machine
run: the VCode outcome depends on it, and the linking statement chooses its outcome after `P`.

* `XPI`: the `ExtSemI` of the calls (`XPI_at`: its call number `n` is `XP … n`, by `rfl`);
* `callsBefore Mm fa base s i`: the call states (`CallPc`) among the first `i` states of the run of
  `Mm` from `s`; `ProphOk K c Mm fa base s P`: at every call state with `sp = c`, `P` of its index
  holds the state's bytes `StackBelow K c`; `prophOf` is such a prophecy of every run
  (`prophOk_prophOf`, from `prophOf_call`);
* `MachEntryP`: `MachEntry` and a prophecy of its run (the callees' budget below the body's `sp`;
  `⟨h, prophOk_prophOf …⟩` from a `MachEntry` `h`: the run's own prophecy);
* `ThmP`: `Thm` with the outcome chosen per prophecy, realised by the machine-side activations
  with that prophecy; `Thm.thmP` (today's statement is the case of one outcome for every
  prophecy), `thmP` (so it holds at every depth).

`WorldEntry` is unchanged: its `place` pins the CLIF slot-byte oracle to `none`
(`LinkSys.PlaceAt`); the oracle built from the prophecies belongs with the CLIF-side items
(`PlaceAt`, `initState_mem`, the correspondence of the local call index and the oracle's global
activation count in `CrunOk`).
-/

namespace E2E

open Backend Backend.Proof

/-! ## The prophecy of a machine run -/

open Classical in
/-- **The calls before step `i`**: the states of the run of `Mm` from `s` before step `i` at a
call instruction (`CallPc`) of `fa` laid out at `base`. -/
noncomputable def callsBefore (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) : Nat → Nat
  | 0 => 0
  | i + 1 => callsBefore Mm fa base s i + if CallPc fa base (Arm.r .PC (runX Mm i s)) then 1 else 0

theorem callsBefore_mono (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) {i j : Nat} (h : i ≤ j) : callsBefore Mm fa base s i ≤ callsBefore Mm fa base s j := by
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (by simp only [callsBefore]; omega)

/-- A call state counts: the calls before a later step are more. -/
theorem callsBefore_lt {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {i j : Nat} (hc : CallPc fa base (Arm.r .PC (runX Mm i s))) (h : i < j) :
    callsBefore Mm fa base s i < callsBefore Mm fa base s j := by
  have h1 : callsBefore Mm fa base s (i + 1) = callsBefore Mm fa base s i + 1 := by
    simp only [callsBefore, hc, ↓reduceIte]
  have := callsBefore_mono Mm fa base s (show i + 1 ≤ j by omega)
  omega

/-- **The prophecy holds at the call states of the run**: with `sp = c` (the activation's body
`sp`), `P` of the state's call index holds its bytes in the `K` bytes below `c`. -/
def ProphOk (K : Nat) (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (P : Nat → BitVec 64 → BitVec 8) : Prop :=
  ∀ i, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ a, StackBelow K c a → (runX Mm i s).mem a = P (callsBefore Mm fa base s i) a

open Classical in
/-- **The prophecy of a run**: call number `n`'s memory. -/
noncomputable def prophOf (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) (n : Nat) : BitVec 64 → BitVec 8 :=
  if h : ∃ i, CallPc fa base (Arm.r .PC (runX Mm i s)) ∧ callsBefore Mm fa base s i = n then
    (runX Mm (Classical.choose h) s).mem
  else fun _ => 0

theorem prophOf_call {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {i : Nat} (hc : CallPc fa base (Arm.r .PC (runX Mm i s))) :
    prophOf Mm fa base s (callsBefore Mm fa base s i) = (runX Mm i s).mem := by
  have h : ∃ j, CallPc fa base (Arm.r .PC (runX Mm j s)) ∧
      callsBefore Mm fa base s j = callsBefore Mm fa base s i := ⟨i, hc, rfl⟩
  rw [prophOf, dite_eq_left h]
  obtain ⟨hj, he⟩ := Classical.choose_spec h
  have : Classical.choose h = i := by
    rcases Nat.lt_trichotomy (Classical.choose h) i with hlt | heq | hgt
    · exact absurd he (Nat.ne_of_lt (callsBefore_lt hj hlt))
    · exact heq
    · exact absurd he (Nat.ne_of_gt (callsBefore_lt hc hgt))
  rw [this]

/-- **Every run has a prophecy.** -/
theorem prophOk_prophOf (K : Nat) (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) : ProphOk K c Mm fa base s (prophOf Mm fa base s) :=
  fun _ hc _ _ _ => by rw [prophOf_call hc]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-! ## The counted external semantics -/

/-- **The calls of an activation of `g` at depth `M` with the prophecies `P`**: call number `n`
is `XP … P n`. -/
noncomputable def XPI (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) : ExtSemI where
  call n := (L.XP κ M g F P n).call
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

theorem XPI_at (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (n : Nat) : (L.XPI κ M g F P).at n = L.XP κ M g F P n := rfl

/-! ## The linking statement -/

/-- **The machine side of an activation of `g` at depth `M` with the prophecies `P`**: `MachEntry`,
and `P` holds at the run's calls from the body (`sp` the body-entry world's) the callees' budget
`κ M g` below the body's `sp`. -/
structure MachEntryP (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (ra : BitVec 64) (s w₀ : Arm.ArmState)
    (P : Nat → BitVec 64 → BitVec 8) : Prop where
  entry : L.MachEntry κ M g F G ra s w₀
  proph : ProphOk (κ M g) (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s P

/-- **The linking statement at depth `M` with prophecies**: `Thm`, the outcome chosen for each
prophecy `P` and realised by every machine-side activation whose run has the prophecy `P`
(`MachEntryP`; with non-interference: every one entered with a body-entry world as in `Thm`). -/
def ThmP (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem) (P : Nat → BitVec 64 → BitVec 8),
    L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntryP κ M g F G ra s w₀ P →
        ∃ n, ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntryP κ M g F G ra s w₀' P →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)

/-- **Today's linking statement is the case of one outcome for every prophecy.** -/
theorem Thm.thmP {M : Nat} (h : L.Thm κ M) : L.ThmP κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' _ hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ := h g hg F vals cs w₀ fuel rvals cm' hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall G ra s hME.entry,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME => hni hN D w₀' hrel hsw hreg hstk G ra s hME.entry⟩

/-- **The linking statement with prophecies at every depth.** -/
theorem thmP (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) (M : Nat) : L.ThmP κ M :=
  Thm.thmP L (L.thm hL hκ M)

end LinkSys

end E2E
