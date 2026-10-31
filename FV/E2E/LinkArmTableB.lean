import FV.E2E.LinkPlaceBCount
import FV.E2E.LinkArmProphDetR
import FV.E2E.LinkArmProphReg
import FV.E2E.BackendWorldPRB

/-!
# The linking statement with the slot-byte oracle (SEM1 item (d), `docs/plans/uninit.md` §5.9)

With the slot-byte oracle `ini` the CLIF outcome of an activation depends on the byte table, which
must be the machine's: entry `k` is the memory at the entry of the `k`-th placed activation with
slots that the run enters (at its entry state, `BodyEntry.mem`: the body-entry world has the entry
memory). The linked machine runs a program callee atomically (`pcall`, `linkedCall` of the callee
machine one level down), so the machine side of the table is recursive in the depth:

* `CallsTo g t h`: the step of `g`'s machine at `t` is a call of the function `h` of `P`
  (`callHook`'s destination: `bl n` with `P.func? n = some h`, or `blr` to `h`'s address);
* `SlotByte h c a`: `a` is a byte of a stack slot of an activation of `h` called with `sp = c`
  (the addresses `initState_memB` gives the CLIF slots);
* `TabUpTo M g s b k N e`: the first `N` steps of `g`'s machine at depth `M` from `s` enter the
  placed activations with slots `k + 1, …, k + e` of the table `b`, and each call `j` (`callsBefore`)
  advances the count by `E j`: by `0` at a call outside `P`, by the callee's own entry (`slotted`,
  whose slot bytes are `b`'s entry, the memory at the call) plus its run's up to its return;
* `TableOf M g s ini`: every prefix of the run before its return agrees with `ini` from
  `ini.next` on;
* `WorldEntryB`: `WorldEntry` with the CLIF entry memory placed with the oracle (`PlaceAtB`);
* `ThmPRB κ M`: for every machine entry `s` (with its own prophecies `prophOf`/`prophStOf`) whose
  table is `ini`'s, a returning CLIF run gives one counted outcome that `s` realises, with the
  machine's count equal to the CLIF counter's advance;
* `XPRBI`: the calls of an activation with both prophecies, guarded by the contracts of the
  invocation of each call (`ExtSemI.guardI`, `CallPostN`), the `XI` of the induction step.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **The machine step of `g`'s code at `t` calls the function `h` of `P`.** -/
def CallsTo (g : Clif.Function) (t : Arm.ArmState) (h : Clif.Function) : Prop :=
  (∃ n, insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some (.bl n) ∧ L.P.func? n = some h) ∨
  ((∃ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some (.blr x)) ∧
    (blrTarget t).bind (symCallee L.Xb L.P) = some h)

/-- **`a` is a stack-slot byte of an activation of `h` called with `sp = c`.** -/
def SlotByte (h : Clif.Function) (c : BitVec 64) (a : Nat) : Prop :=
  ∃ p ∈ h.slots,
    (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
        ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) ≤ a ∧
      a < (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
        ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) + p.2.size

/-- **The machine-side table of a run prefix**: the first `N` steps of `g`'s machine at depth `M`
from `s` enter the placed activations with slots `k + 1, …, k + e` of `b` (see the module doc). -/
def TabUpTo : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat →
    Prop
  | 0, g, s, _, _, N, e => e = 0 ∧ ∀ i < N, ∀ h, ¬ L.CallsTo g (runX (L.mach 0 g) i s) h
  | M + 1, g, s, b, k, N, e => ∃ E : Nat → Nat,
      e = Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s N) ∧
      ∀ i < N, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)) →
        ((∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h) →
          E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) = 0) ∧
        ∀ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
          let t := runX (L.mach (M + 1) g) i s
          let j := callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i
          (slotted h = 1 → ∀ a, L.SlotByte h (spv t) a →
            b (k + Clif.sumTo E j + 1) a = t.mem (BitVec.ofNat 64 a)) ∧
          slotted h ≤ E j ∧
          ∃ N', RetOf (L.A h) t (runX (L.mach M h) N' (enterAt (L.A h) t)) ∧
            (∀ N'' < N', ¬ RetOf (L.A h) t (runX (L.mach M h) N'' (enterAt (L.A h) t))) ∧
            TabUpTo M h (enterAt (L.A h) t) b (k + Clif.sumTo E j + slotted h) N'
              (E j - slotted h)

/-- `g`'s activation entered at `s` has returned in `t` (`RetOf` of its call). -/
def RetAt (g : Clif.Function) (s t : Arm.ArmState) : Prop :=
  Arm.r .PC t = xreg 30 s ∧ Arm.r .ERR t = .None ∧ t.program = (L.A g).fb.program (L.A g).base ∧
    spv t = spv s

/-- **The run's table is `ini`'s**: every prefix before the return enters the placed activations
with slots `ini.next + 1, …` of `ini.bytes`. -/
def TableOf (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (ini : Clif.SlotInit) : Prop :=
  ∀ N, (∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    ∃ e, L.TabUpTo M g s ini.bytes ini.next N e

/-- **The world side of an activation under the slot-byte oracle**: `WorldEntry` with the CLIF
entry memory placed with `ini`. -/
structure WorldEntryB (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State) (w₀ : Arm.ArmState)
    (ini : Clif.SlotInit) : Prop where
  clif : ClifEntry g vals cs
  rel : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
    g (spv w₀) cs.frame.slots cs.mem w₀
  args : ArgsAtEntry F g.sig vals w₀
  room : κ M g ≤ (spv w₀).toNat
  dead : ∀ a, StackBelow (κ M g) (spv w₀) a → F a ∧ ¬ L.Img a
  align : (spv w₀).toNat % 16 = 0
  img : ∀ a, L.Img a → F a
  place : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) ini

/-- Without program callees with slots `WorldEntryB` is `WorldEntry`. -/
theorem WorldEntryB.toWorldEntry {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {vals : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState}
    {ini : Clif.SlotInit} (h : L.WorldEntryB κ M g F vals cs w₀ ini) (hN : ¬ L.NeedSlots) :
    L.WorldEntry κ M g F vals cs w₀ :=
  ⟨h.clif, h.rel, h.args, h.room, h.dead, h.align, h.img, fun hS => absurd hS hN⟩

/-- **The linking statement at depth `M` under the slot-byte oracle**: for every machine entry `s`
of `g` (with the prophecies of its own run) whose run's table is `ini`'s, and every CLIF entry
placed with `ini` related to the same body-entry world, a returning CLIF run gives one outcome
that `s` realises; the machine's table count `e` up to the return is the CLIF counter's
advance. -/
def ThmPRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s) →
    L.TableOf M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (n e : Nat),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
      PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
      L.TabUpTo M g s ini.bytes ini.next n e ∧ (L.NeedSlots → Clif.NextAdv cs.mem cm' e)

/-- **The calls of an activation of `g` under the slot-byte oracle**: `XPRI` with call `n`
guarded by the contracts of the CLIF invocation of call `n` of the run from `cs` under `env`
(`CallPostN`), for the body `sp` `c`. -/
noncomputable def XPRBI (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (env : Clif.Env) (cs : Clif.State) (c : BitVec 64) : ExtSemI :=
  (L.XPRI κ M g F P R).guardI (CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
    (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
    L.Xb.sym)

/-! ## Prefixes -/

/-- The empty prefix enters no activation. -/
theorem tabUpTo_zero (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (b : Nat → Nat → BitVec 8)
    (k : Nat) : L.TabUpTo M g s b k 0 0 := by
  cases M with
  | zero => exact ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ M => exact ⟨fun _ => 0, by simp [callsBefore, Clif.sumTo],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **A shorter prefix has a table** (the same per-call counts). -/
theorem tabUpTo_mono {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {b : Nat → Nat → BitVec 8}
    {k N e : Nat} (h : L.TabUpTo M g s b k N e) {N' : Nat} (hN : N' ≤ N) :
    ∃ e', L.TabUpTo M g s b k N' e' := by
  cases M with
  | zero => exact ⟨0, rfl, fun i hi => h.2 i (by omega)⟩
  | succ M =>
    obtain ⟨E, -, hE⟩ := h
    exact ⟨_, E, rfl, fun i hi => hE i (by omega)⟩

/-- The table of a prefix at depth `0` is empty. -/
theorem tabUpTo_zero_depth {g : Clif.Function} {s : Arm.ArmState} {b : Nat → Nat → BitVec 8}
    {k N e : Nat} (h : L.TabUpTo 0 g s b k N e) : e = 0 := h.1

/-- A run that has returned at its entry has the table of every oracle. -/
theorem tableOf_of_retAt {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    (h : L.RetAt g s s) (ini : Clif.SlotInit) : L.TableOf M g s ini := by
  intro N hN
  cases N with
  | zero => exact ⟨0, L.tabUpTo_zero M g s ini.bytes ini.next⟩
  | succ N => exact absurd h (hN 0 (Nat.succ_pos N))

/-- **Stage 2 interface**: where `XPR`'s result for call `n` is accepted by the contracts of the
invocation of call `n`, `XPRBI` returns it. -/
theorem XPRBI_of {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (hx : (L.XPR κ M g F P R n).call d uses w = some r)
    (hq : CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym n d uses w r) :
    ((L.XPRBI κ M g F P R env cs c).at n).call d uses w = some r :=
  ExtSem.guard_of (X := (L.XPRI κ M g F P R).at n) hx hq

end LinkSys

end E2E
