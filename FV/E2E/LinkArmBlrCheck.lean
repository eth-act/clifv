import FV.E2E.LinkArmTableB
import FV.E2E.LinkArmStepX30
import FV.E2E.LinkArmOracleAt

/-!
# The compiled-code check that no `blr` jumps through `x29`/`x30`, and the program calls of two
locked states (SEM1 #537, `docs/plans/uninit.md` §5.9, determinism step)

`CallsTo g u h` (the table's notion of a program call) reads the target of a `blr` from the
machine: `blrTarget` decodes the four code bytes at the pc **from memory** and returns the
register the decoded `blr` names. Two states of the machine lock (`StEqOutX Z`: equal but for
`x30` and the bytes in `Z`) agree on every register but `x30`, so their `blr` targets agree when
the code bytes decode as the laid-out `blr` in both states and that `blr` does not name `x30`.
`x30Free` exempts `blr` (the call writes `x30`), so a separate check is needed; Cranelift's
register allocator never assigns `x29`/`x30` to a call target (`locOk_int`: `n < 29`), and the
check below states exactly the hypothesis of `blrTarget_of`:

* `Insn.blrLow`, **`FnAsm.blrLow fa`**: every `blr` line jumps through `x0`–`x28` (decidable,
  measured on fv-demo and the survey, `docs/plans/uninit.md` §5.9);
* `blrLow_line` (soundness), **`blrTarget_eq_of_lock`**: at a `blr` line, two locked states whose
  memories hold the code words have the same `blr` target;
* **`LinkSys.callsTo_iff_of_lock`**: two locked states holding the code image (`Img`, as every
  state of a linked run does: `Ok.imgCode`) call the same program functions;
* **`LinkSys.slotByte_eq_of_lock`**: at a call made with `sp = c`, the callee's slot bytes are in
  the `K` bytes below `c` when the callee's frame fits in `K` (the κ budget: `Budget` gives
  `frameDrop (L.A h).af ≤ κ M g` for a callee `h` of `g` at depth `M`), so two states equal on
  that dead stack agree on them.
-/

namespace E2E

open Backend Backend.Proof

/-- One line's check: a `blr` jumps through `x0`–`x28`. -/
def _root_.Backend.Insn.blrLow : Insn → Bool
  | .blr (.x n) => decide (n < 29)
  | .blr _ => false
  | _ => true

/-- **The check on compiled code**: every `blr` line of `fa` jumps through `x0`–`x28`. -/
def _root_.Backend.FnAsm.blrLow (fa : FnAsm) : Bool :=
  fa.lines.toList.all fun l => match l with
    | .ins x _ => x.blrLow
    | _ => true

/-- **Soundness of the check.** -/
theorem blrLow_line {fa : FnAsm} (h : fa.blrLow = true) {j : Nat} {r : Reg}
    {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins (.blr r) t)) :
    ∃ n, r = .x n ∧ n < 29 := by
  have hm : Line.ins (.blr r) t ∈ fa.lines.toList := List.mem_of_getElem? hj
  have := List.all_eq_true.mp h _ hm
  cases r with
  | x n => exact ⟨n, rfl, by simpa [Insn.blrLow] using this⟩
  | _ => simp [Insn.blrLow] at this

/-- The line of an instruction found by `insnAt`. -/
theorem insnAt_line_of {fa : FnAsm} {base pc : BitVec 64} {i : Insn}
    (h : insnAt fa base pc = some i) :
    ∃ j t, fa.lines.toList[j]? = some (.ins i t) ∧
      base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) = pc := by
  unfold insnAt at h
  split at h
  · rename_i hex
    obtain ⟨t, h1, h2⟩ := Classical.choose_spec (Classical.choose_spec hex)
    cases h
    exact ⟨_, t, h1, h2⟩
  · cases h

/-- **Two locked states at a `blr` line have the same `blr` target** when both memories hold the
code words. -/
theorem blrTarget_eq_of_lock {fa : FnAsm} {fb : FnBin} {base : BitVec 64}
    {lm : Std.HashMap Lbl Nat} (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hc : fa.blrLow = true) {Z : BitVec 64 → Prop} {u u' : Arm.ArmState} (hlk : StEqOutX Z u u')
    {j : Nat} {r : Reg} {tt : Option Clif.TrapCode}
    (hj : fa.lines.toList[j]? = some (.ins (.blr r) tt))
    (hpc : Arm.r .PC u = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (hmem : ∀ k w, fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) u = w)
    (hmem' : ∀ k w, fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) u' = w) :
    blrTarget u = blrTarget u' := by
  obtain ⟨n, rfl, hn⟩ := blrLow_line hc hj
  have hpc' : Arm.r .PC u' = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) := by
    rw [← hlk.1 .PC (by simp)]; exact hpc
  rw [blrTarget_of hl hm hj hn hpc hmem, blrTarget_of hl hm hj hn hpc' hmem']
  have hne : Arm.StateField.GPR (rnum n) ≠ .GPR 30#5 := by
    intro e
    injection e with e
    exact rnum_ne (a := n) (b := 30) (by omega) (by omega) (by omega) e
  rw [hlk.1 _ hne]

/-- **The machine reads its external semantics only through `sym`** (so the activation's
machine `R.step`, at `X := XI.at 0`, is the link's `L.mach M g` when the symbols agree). -/
theorem armStepX_congr_sym {X X' : ExtSem} (hs : X.sym = X'.sym) (H : ArmHooks) (fa : FnAsm) :
    ArmStepX X H fa = ArmStepX X' H fa := by
  funext s
  simp only [ArmStepX, hs]

namespace LinkSys

variable (L : LinkSys)

/-- **Two locked states holding the code image call the same program functions.** -/
theorem callsTo_iff_of_lock (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {Z : BitVec 64 → Prop} {u u' : Arm.ArmState}
    (hlk : StEqOutX Z u u') (himg : ∀ a, L.Img a → u.mem a = L.imgMem a)
    (himg' : ∀ a, L.Img a → u'.mem a = L.imgMem a) (h : Clif.Function) :
    L.CallsTo g u h ↔ L.CallsTo g u' h := by
  have hpc : Arm.r .PC u = Arm.r .PC u' := hlk.1 .PC (by simp)
  have hb : ∀ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some (.blr x) →
      blrTarget u = blrTarget u' := by
    intro x hx
    obtain ⟨j, tt, hj, hpj⟩ := insnAt_line_of hx
    have hcc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hcc.layout
    exact blrTarget_eq_of_lock hcc.layout hlm hc hlk hj hpj.symm
      (fun k w hk => hL.imgCode g hg u himg k w hk) (fun k w hk => hL.imgCode g hg u' himg' k w hk)
  unfold CallsTo
  rw [← hpc]
  constructor
  · rintro (h1 | ⟨⟨x, hi⟩, ht⟩)
    · exact .inl h1
    · exact .inr ⟨⟨x, hi⟩, by rw [← hb x hi]; exact ht⟩
  · rintro (h1 | ⟨⟨x, hi⟩, ht⟩)
    · exact .inl h1
    · exact .inr ⟨⟨x, hi⟩, by rw [hb x hi]; exact ht⟩

/-- **The callee's slot bytes at a call are in the dead stack** (`K` bytes below the call's `sp`)
when the callee's frame fits in `K`; two states equal there agree on them. -/
theorem slotByte_eq_of_lock (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hcal : L.Callee g h) {K : Nat} (hK : frameDrop (L.A h).af ≤ K) {c : BitVec 64}
    (hroom : frameDrop (L.A h).af ≤ c.toNat) {u u' : Arm.ArmState}
    (hdead : ∀ a, StackBelow K c a → u.mem a = u'.mem a) {a : Nat} (ha : L.SlotByte h c a) :
    u.mem (BitVec.ofNat 64 a) = u'.mem (BitVec.ofNat 64 a) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := L.slotByte_below hL hg hcal hroom ha
  exact hdead _ ⟨h1, by omega⟩

end LinkSys

end E2E
