import Crates.BinaryWitness
import FV.E2E.ExecBytes

/-! # Non-vacuity of the theorem about the executable's own words

`E2E.ExecBytes.binary_correct_exec` (L3) assumes, besides the premises of
`binary_correct_of_checks_acyclic`, the per-state facts `RunOk` of the model's run. Here every
premise, `RunOk` included, holds together on the `a_arith` executable (`Crates.BinaryWitness`):
outside code calls its Lean-compiled `core::num::<i32>::wrapping_add` (`stp x29, x30, [sp, #-16]!;
mov x29, sp; add w0, w0, w1; ldp x29, x30, [sp], #16; ret`) with `2` and `3`. The model's run is
computed state by state (`S1` … `S5`, the return); at each state before the return `StepOk`
holds: the word decodes to the instruction the model runs, and the instruction reads no relocated
instruction byte (the stack is above `2^32`, every relocated byte below it and outside the entry's
code). The theorem then gives the **executable machine's** return to the caller with `5` in x0.
-/

namespace Crates.BinaryExecWitness

open E2E E2E.LinkCheck E2E.Binary E2E.BinCheck E2E.ExecBytes Backend Backend.Proof
open Crates.BinaryWitness

/-! ## Simulation facts of single instructions (any input) -/

section SimLemmas

variable {J : LinkInput}

theorem sim_write_mem {m e : Arm.ArmState} (h : Sim J m e) (a : BitVec 64) (b : BitVec 8) :
    Sim J (Arm.write_mem a b m) (Arm.write_mem a b e) := by
  refine ⟨fun fld => by rw [Arm.r_of_write_mem, Arm.r_of_write_mem]; exact h.1 fld, fun x hx => ?_⟩
  simp only [Arm.write_mem, Arm.write_store]
  split
  · rfl
  · exact h.2 x hx

theorem sim_write_mem_bytes : ∀ (k : Nat) (a : BitVec 64) (v : BitVec (k * 8)) {m e : Arm.ArmState},
    Sim J m e → Sim J (Arm.write_mem_bytes k a v m) (Arm.write_mem_bytes k a v e)
  | 0, _, _, _, _, h => h
  | k + 1, _, _, _, _, h => by
    simp only [Arm.write_mem_bytes]
    exact sim_write_mem_bytes k _ _ (sim_write_mem h _ _)

theorem sim_r {m e : Arm.ArmState} (h : Sim J m e) (fld : Arm.StateField) :
    Arm.r fld e = Arm.r fld m := h.1 fld

/-- `add w0, w0, w1` on the machine. -/
theorem exec_add_w0 (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.aluRRR .add false (.x 0) (.x 0) (.x 1)).toArmInst env = .ok a ∧
      Arm.exec_inst a s = Arm.w (.GPR 0#5)
        (BitVec.setWidth 64 (BitVec.setWidth 32 (Arm.r (.GPR 0#5) s) +
          BitVec.setWidth 32 (Arm.r (.GPR 1#5) s)))
        (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.fst_AddWithCarry_eq_add]

theorem sim_stp {env : Env} {a : Arm.ArmInst}
    (ha : (Insn.stp Reg.fp Reg.lr (.spPreIndexed (-16))).toArmInst env = .ok a)
    {m e : Arm.ArmState} (hal : (spOf m).toNat % 16 = 0) (h : Sim J m e) :
    Sim J (Arm.exec_inst a m) (Arm.exec_inst a e) := by
  have hal' : (spOf e).toNat % 16 = 0 := by rw [spOf, sim_r h]; exact hal
  obtain ⟨a1, h1, e1⟩ := exec_stp_fplr env m ((checkSP_iff m).2 hal)
  obtain ⟨a2, h2, e2⟩ := exec_stp_fplr env e ((checkSP_iff e).2 hal')
  rw [ha] at h1 h2; cases h1; cases h2
  rw [e1, e2]
  simp only [spOf, xreg, sim_r h]
  exact sim_w (sim_w (sim_write_mem_bytes _ _ _ h) _ _) _ _

theorem sim_mov {env : Env} {a : Arm.ArmInst}
    (ha : (Insn.mov true Reg.fp .sp).toArmInst env = .ok a) {m e : Arm.ArmState} (h : Sim J m e) :
    Sim J (Arm.exec_inst a m) (Arm.exec_inst a e) := by
  obtain ⟨a1, h1, e1⟩ := exec_mov_fp_sp env m
  obtain ⟨a2, h2, e2⟩ := exec_mov_fp_sp env e
  rw [ha] at h1 h2; cases h1; cases h2
  rw [e1, e2]
  simp only [spOf, sim_r h]
  exact sim_w (sim_w h _ _) _ _

theorem sim_add {env : Env} {a : Arm.ArmInst}
    (ha : (Insn.aluRRR .add false (.x 0) (.x 0) (.x 1)).toArmInst env = .ok a) {m e : Arm.ArmState}
    (h : Sim J m e) : Sim J (Arm.exec_inst a m) (Arm.exec_inst a e) := by
  obtain ⟨a1, h1, e1⟩ := exec_add_w0 env m
  obtain ⟨a2, h2, e2⟩ := exec_add_w0 env e
  rw [ha] at h1 h2; cases h1; cases h2
  rw [e1, e2]
  simp only [sim_r h]
  exact sim_w (sim_w h _ _) _ _

theorem sim_ldp {env : Env} {a : Arm.ArmInst}
    (ha : (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok a)
    {m e : Arm.ArmState} (hal : (spOf m).toNat % 16 = 0)
    (hR : ∀ k < 16, ¬ RelocAt J (spOf m + BitVec.ofNat 64 k)) (h : Sim J m e) :
    Sim J (Arm.exec_inst a m) (Arm.exec_inst a e) := by
  have hal' : (spOf e).toNat % 16 = 0 := by rw [spOf, sim_r h]; exact hal
  obtain ⟨a1, h1, e1⟩ := exec_ldp_fplr env m ((checkSP_iff m).2 hal)
  obtain ⟨a2, h2, e2⟩ := exec_ldp_fplr env e ((checkSP_iff e).2 hal')
  rw [ha] at h1 h2; cases h1; cases h2
  rw [e1, e2]
  have hrd : Arm.read_mem_bytes 16 (spOf m) e = Arm.read_mem_bytes 16 (spOf m) m :=
    rmb_congr 16 _ fun k hk => h.2 _ (hR k hk)
  simp only [spOf, sim_r h] at hrd ⊢
  rw [hrd]
  exact sim_w (sim_w (sim_w (sim_w h _ _) _ _) _ _) _ _

theorem sim_ret {env : Env} {a : Arm.ArmInst} (ha : Insn.ret.toArmInst env = .ok a)
    {m e : Arm.ArmState} (h : Sim J m e) : Sim J (Arm.exec_inst a m) (Arm.exec_inst a e) := by
  obtain ⟨a1, h1, e1⟩ := exec_ret env m
  obtain ⟨a2, h2, e2⟩ := exec_ret env e
  rw [ha] at h1 h2; cases h1; cases h2
  rw [e1, e2]
  simp only [xreg, sim_r h]
  exact sim_w h _ _

end SimLemmas

/-! ## `StepOk` at an unhooked instruction of a function without relocations (any input) -/

section StepOkPlain

variable {J : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The machine step at an unhooked instruction line, from an exec lemma of the instruction. -/
theorem mach_line {Mx : Nat} {g : Clif.Function} (hF : FnOk J file g) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art J g).fa.lines.toList[j]? = some (.ins i t))
    (hh : i.hooked = false) {s s' : Arm.ArmState}
    (hprog : s.program = (art J g).fb.program (art J g).base) (herr : Arm.r .ERR s = .None)
    (hpc : Arm.r .PC s = wAt (art J g) (lineOffset (art J g).fa.lines.toList j))
    (hx : ∀ env, ∃ a, i.toArmInst env = .ok a ∧ Arm.exec_inst a s = s') :
    (sys J B).mach Mx g s = s' := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨a, ha, hst⟩ := armStepX_ins (X := (sys J B).Xb) (H := (sys J B).hooks Mx) hF.layout hm
    (by have := hF.fits; omega) hj hh hprog hpc herr
  obtain ⟨a', ha', hx'⟩ := hx ⟨lineOffset (art J g).fa.lines.toList j, (lm[·]?)⟩
  rw [ha] at ha'; cases ha'
  show ArmStepX (sys J B).Xb ((sys J B).hooks Mx) (art J g).fa s = s'
  rw [hst, hx']

/-- **`StepOk` at an unhooked, unrelocated instruction** of a function without relocations: the
pc's site, and the instruction's simulation property (`hP`) for the word of its encoding. -/
theorem stepOk_plain {Mx : Nat} {g : Clif.Function} (hF : FnOk J file g)
    (hrel : (art J g).fb.relocs = []) {j : Nat} {i0 : Insn} {t : Option Clif.TrapCode}
    (hj : (art J g).fa.lines.toList[j]? = some (.ins i0 t)) (hr : i0.reloc? = none)
    (hh : i0.hooked = false) {m : Arm.ArmState} (herr : Arm.r .ERR m = .None)
    (hprog : m.program = (art J g).fb.program (art J g).base)
    (hpc : Arm.r .PC m = wAt (art J g) (lineOffset (art J g).fa.lines.toList j))
    (hsite : siteAt J (Arm.r .PC m) = some i0)
    (hP : ∀ env a, i0.toArmInst env = .ok a → ∀ e, Sim J m e →
      Sim J (Arm.exec_inst a m) (Arm.exec_inst a e))
    (hplain : ∀ k < 4, ¬ RelocAt J (Arm.r .PC m + BitVec.ofNat 64 k)) :
    StepOk J B file Mx g m := by
  have hi0 : insnAt (art J g).fa (art J g).base (Arm.r .PC m) = some i0 := by
    rw [hpc]; exact insnAt_of_line hF hj
  have hno : ∀ i, insnAt (art J g).fa (art J g).base (Arm.r .PC m) = some i → i.hooked = true →
      False := fun i h hk => by
    rw [hi0] at h; cases h; rw [hh] at hk; cases hk
  refine ⟨herr, hprog, ⟨i0, hi0, hsite, .inl hr⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => hplain⟩
  · intro rl hrl
    rw [hrel] at hrl; cases hrl
  · intro i hi _ a ha e hs
    obtain rfl : i = i0 := by rw [hi0] at hi; cases hi; rfl
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
    obtain ⟨w, hw, hf⟩ := fileWord_plain hF hm hj hr
    obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
    rw [hpc, hf, Option.bind_some, hd] at ha
    cases ha
    exact hP _ _ ha' e hs
  · intro d e hd
    rcases hd with ⟨n, hn, -⟩ | ⟨⟨x, hx⟩, -⟩
    · exact (hno _ hn rfl).elim
    · exact (hno _ hx rfl).elim
  · intro tmp rn n e hn
    exact (hno _ hn rfl).elim
  · intro rl hrl
    rw [hrel] at hrl; cases hrl
  · intro x h hx
    exact (hno _ hx rfl).elim

/-- No call of the program at an unhooked instruction. -/
theorem noCall_plain {g : Clif.Function} (hF : FnOk J file g) {j : Nat} {i0 : Insn}
    {t : Option Clif.TrapCode} (hj : (art J g).fa.lines.toList[j]? = some (.ins i0 t))
    (hh : i0.hooked = false) {m : Arm.ArmState}
    (hprog : m.program = (art J g).fb.program (art J g).base)
    (hpc : Arm.r .PC m = wAt (art J g) (lineOffset (art J g).fa.lines.toList j)) (h : Clif.Function) :
    ¬ CallsAt J B g m h := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  have hi0 : insnAt (art J g).fa (progBase m) (Arm.r .PC m) = some i0 := by
    rw [progBase_of hF hm hprog hj, hpc]; exact insnAt_of_line hF hj
  rintro (⟨n, hn, -⟩ | ⟨⟨x, hx⟩, -⟩)
  · rw [hi0] at hn; cases hn; cases hh
  · rw [hi0] at hx; cases hx; cases hh

end StepOkPlain

/-! ## The entry's code in the `a_arith` executable -/

/-- The line `o` is the instruction `i`. -/
def lineIs (o : Option Line) (i : Insn) : Bool :=
  match o with
  | some (.ins i' _) => decide (i' = i)
  | _ => false

theorem lineIs_spec {o : Option Line} {i : Insn} (h : lineIs o i = true) :
    ∃ t, o = some (.ins i t) := by
  unfold lineIs at h
  split at h
  · rename_i i' t
    simp only [decide_eq_true_eq] at h
    exact ⟨t, by rw [h]⟩
  · cases h

abbrev L : List Line := (art I f).fa.lines.toList

def iStp : Insn := .stp Reg.fp Reg.lr (.spPreIndexed (-16))
def iMov : Insn := .mov true Reg.fp .sp
def iAdd : Insn := .aluRRR .add false (.x 0) (.x 0) (.x 1)
def iLdp : Insn := .ldp Reg.fp Reg.lr (.spPostIndexed 16)

/-- The entry's code start. -/
abbrev bse : Nat := (art I f).base.toNat

/-- The facts of the entry's code decided on the executable's data: its lines, their offsets,
no relocation, and every other function's code and every relocated byte of the program away
from the entry's 20 code bytes (relocated bytes below `2^32`). -/
def codeB : Bool :=
  lineIs L[1]? iStp && lineIs L[2]? iMov && lineIs L[4]? iAdd && lineIs L[5]? iLdp &&
  lineIs L[6]? .ret &&
  lineOffset L 1 == 0 && lineOffset L 2 == 4 && lineOffset L 4 == 8 && lineOffset L 5 == 12 &&
  lineOffset L 6 == 16 &&
  (art I f).fb.relocs.isEmpty && f.name == n && decide (bse + 20 ≤ 2 ^ 32) &&
  (tabOf I.results).all (fun e => e.1.name == n ||
    decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ bse ∨ bse + 20 ≤ e.2.base.toNat)) &&
  (tabOf I.results).all (fun e => e.2.fb.relocs.all fun rl => (List.range 4).all fun k =>
    decide ((wAt e.2 (rl.offset + k)).toNat < 2 ^ 32 ∧
      ((wAt e.2 (rl.offset + k)).toNat < bse ∨ bse + 20 ≤ (wAt e.2 (rl.offset + k)).toNat)))

theorem codeB_true : codeB = true := by native_decide

theorem code :
    (∃ t, L[1]? = some (.ins iStp t)) ∧ (∃ t, L[2]? = some (.ins iMov t)) ∧
    (∃ t, L[4]? = some (.ins iAdd t)) ∧ (∃ t, L[5]? = some (.ins iLdp t)) ∧
    (∃ t, L[6]? = some (.ins .ret t)) ∧
    lineOffset L 1 = 0 ∧ lineOffset L 2 = 4 ∧ lineOffset L 4 = 8 ∧ lineOffset L 5 = 12 ∧
    lineOffset L 6 = 16 ∧ (art I f).fb.relocs = [] ∧ f.name = n ∧ bse + 20 ≤ 2 ^ 32 ∧
    (∀ e ∈ tabOf I.results, e.1.name ≠ n →
      e.2.base.toNat + 4 * e.2.fb.words.size ≤ bse ∨ bse + 20 ≤ e.2.base.toNat) ∧
    (∀ a, RelocAt I a → a.toNat < 2 ^ 32 ∧ (a.toNat < bse ∨ bse + 20 ≤ a.toNat)) := by
  have h := codeB_true
  simp only [codeB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  refine ⟨lineIs_spec h1, lineIs_spec h2, lineIs_spec h3, lineIs_spec h4, lineIs_spec h5, h6, h7,
    h8, h9, h10, List.isEmpty_iff.mp h11, h12, h13, fun e he hne => ?_, fun a ha => ?_⟩
  · have := List.all_eq_true.mp h14 e he
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this.resolve_left hne
  · obtain ⟨e, he, rl, hrl, k, hk, rfl⟩ := ha
    have := List.all_eq_true.mp (List.all_eq_true.mp h15 e he) rl hrl
    have := List.all_eq_true.mp this k (List.mem_range.2 hk)
    simpa using this

theorem toNat_wAt {o : Nat} (ho : o ≤ 20) : (wAt (art I f) o).toNat = bse + o := by
  have := code.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [bse] at this ⊢
  simp only [wAt, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : o < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- The words of the entry's code are no relocated bytes. -/
theorem plain_f {o : Nat} (ho : o ≤ 16) : ∀ k < 4, ¬ RelocAt I (wAt (art I f) o + BitVec.ofNat 64 k) := by
  intro k hk hR
  have := (code.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hR).2
  have h1 := toNat_wAt (o := o) (by omega)
  have h2 := code.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The site lookup at the entry's code finds the entry's instruction (no other function's code
is there). -/
theorem siteAt_f {file : ByteArray} (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {o : Nat} (ho : o < 20)
    {i : Insn} (hi : insnAt (art I f).fa (art I f).base (wAt (art I f) o) = some i) :
    siteAt I (wAt (art I f) o) = some i := by
  have hfm := (Clif.Program.func?_some facts.1).1
  have hfn := code.2.2.2.2.2.2.2.2.2.2.2.1
  have ha := toNat_wAt (o := o) (by omega)
  unfold siteAt
  split
  · rename_i hex
    have hs := hex.choose_spec
    generalize hex.choose = g at hs ⊢
    obtain ⟨hg, hsome⟩ := hs
    suffices art I g = art I f by rw [this]; exact hi
    by_cases hgn : g.name = n
    · simp only [art, artOf, hgn, ← hfn]
    · exfalso
      obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hi'
      have hl := line_lt (hF g hg) hj
      have hfit := (hF g hg).fits
      have hd : (art I g).base.toNat + 4 * (art I g).fb.words.size ≤ bse ∨
          bse + 20 ≤ (art I g).base.toNat :=
        code.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (tab_mem (okB_names Crates.AArithAbort.okB_input) hg) hgn
      have := congrArg BitVec.toNat hpc
      rw [ha, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lineOffset _ j < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
  · rename_i hne
    exact absurd ⟨f, hfm, by rw [hi]; rfl⟩ hne

/-! ## The model's run of the entry -/

section Run

variable (c : Arm.ArmState)

def S1 : Arm.ArmState := Arm.w .PC (Arm.r .PC c + 4#64) (Arm.w (.GPR 31#5) (spOf c - 16#64)
    (Arm.write_mem_bytes 16 (spOf c - 16#64) (xreg 30 c ++ xreg 29 c) c))

def S2 : Arm.ArmState :=
  Arm.w (.GPR 29#5) (spOf (S1 c)) (Arm.w .PC (Arm.r .PC (S1 c) + 4#64) (S1 c))

def S3 : Arm.ArmState := Arm.w (.GPR 0#5)
    (BitVec.setWidth 64 (BitVec.setWidth 32 (Arm.r (.GPR 0#5) (S2 c)) +
      BitVec.setWidth 32 (Arm.r (.GPR 1#5) (S2 c))))
    (Arm.w .PC (Arm.r .PC (S2 c) + 4#64) (S2 c))

def S4 : Arm.ArmState :=
  Arm.w .PC (Arm.r .PC (S3 c) + 4#64) (Arm.w (.GPR 31#5) (spOf (S3 c) + 16#64)
    (Arm.w (.GPR 30#5) ((Arm.read_mem_bytes 16 (spOf (S3 c)) (S3 c)).extractLsb' 64 64)
      (Arm.w (.GPR 29#5) ((Arm.read_mem_bytes 16 (spOf (S3 c)) (S3 c)).extractLsb' 0 64) (S3 c))))

def S5 : Arm.ArmState := Arm.w .PC (xreg 30 (S4 c)) (S4 c)

/-- The entry state of the model's run. -/
structure Entry : Prop where
  prog : c.program = (art I f).fb.program (art I f).base
  err : Arm.r .ERR c = .None
  pc : Arm.r .PC c = (art I f).base
  sp : spOf c = sp0

variable {c}

theorem err_S (h : Entry c) : Arm.r .ERR (S1 c) = .None ∧ Arm.r .ERR (S2 c) = .None ∧
    Arm.r .ERR (S3 c) = .None ∧ Arm.r .ERR (S4 c) = .None ∧ Arm.r .ERR (S5 c) = .None := by
  simp [S5, S4, S3, S2, S1, Arm.r_of_w_different, Arm.r_of_write_mem_bytes, h.err]

theorem prog_S : (S1 c).program = c.program ∧ (S2 c).program = c.program ∧
    (S3 c).program = c.program ∧ (S4 c).program = c.program ∧ (S5 c).program = c.program := by
  simp [S5, S4, S3, S2, S1, Arm.w_program, Arm.write_mem_bytes_program]

theorem sp_S : spOf (S1 c) = spOf c - 16#64 ∧ spOf (S2 c) = spOf c - 16#64 ∧
    spOf (S3 c) = spOf c - 16#64 ∧ spOf (S4 c) = spOf c - 16#64 + 16#64 := by
  simp [S4, S3, S2, S1, spOf, Arm.r_of_w_different, Arm.r_of_w_same, Arm.r_of_write_mem_bytes]

theorem pc_S (h : Entry c) : Arm.r .PC c = wAt (art I f) 0 ∧ Arm.r .PC (S1 c) = wAt (art I f) 4 ∧
    Arm.r .PC (S2 c) = wAt (art I f) 8 ∧ Arm.r .PC (S3 c) = wAt (art I f) 12 ∧
    Arm.r .PC (S4 c) = wAt (art I f) 16 := by
  simp only [S4, S3, S2, S1, wAt, h.pc, Arm.r_of_w_same, Arm.r_of_w_different (show Arm.StateField.PC ≠ .GPR 0#5 by simp),
    Arm.r_of_w_different (show Arm.StateField.PC ≠ .GPR 29#5 by simp)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | bv_omega

theorem rmb_S3 : Arm.read_mem_bytes 16 (spOf c - 16#64) (S3 c) = xreg 30 c ++ xreg 29 c := by
  simp only [S3, S2, S1, Arm.read_mem_bytes_of_w]
  exact Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)

theorem extract_hi (x y : BitVec 64) : (x ++ y).extractLsb' 64 64 = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hi]

/-- The model's activation has returned at `S5`. -/
theorem returned_S5 (h : Entry c) : Returned (art I f) c (S5 c) := by
  obtain ⟨-, -, hs3, hs4⟩ := sp_S (c := c)
  refine ⟨?_, (err_S h).2.2.2.2, prog_S.2.2.2.2.trans h.prog, ?_⟩
  · simp only [S5, Arm.r_of_w_same]
    simp only [S4, xreg, Arm.r_of_w_different (show Arm.StateField.GPR 30#5 ≠ .PC by simp),
      Arm.r_of_w_different (show Arm.StateField.GPR (BitVec.ofNat 5 30) ≠ .GPR 31#5 by simp),
      Arm.r_of_w_same]
    rw [hs3, rmb_S3, extract_hi]; rfl
  · simp only [spv, S5, Arm.r_of_w_different (show Arm.StateField.GPR 31#5 ≠ .PC by simp)]
    rw [show Arm.r (.GPR 31#5) (S4 c) = spOf (S4 c) from rfl, hs4, spOf]
    bv_omega

variable {file : ByteArray} (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
include hF

theorem fnOk_f : FnOk I file f := hF f (Clif.Program.func?_some facts.1).1

/-- `StepOk` at an instruction of the entry's code. -/
theorem stepOk_at {B : BaseEnv} {Mx : Nat} {m : Arm.ArmState} {j o : Nat} {i0 : Insn}
    {t : Option Clif.TrapCode} (hj : L[j]? = some (.ins i0 t)) (ho : lineOffset L j = o)
    (ho16 : o ≤ 16) (hh : i0.hooked = false) (hr : i0.reloc? = none) (herr : Arm.r .ERR m = .None)
    (hprog : m.program = (art I f).fb.program (art I f).base)
    (hpc : Arm.r .PC m = wAt (art I f) o)
    (hP : ∀ env a, i0.toArmInst env = .ok a → ∀ e, Sim I m e →
      Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)) :
    StepOk I B file Mx f m :=
  stepOk_plain (fnOk_f hF) code.2.2.2.2.2.2.2.2.2.2.1 hj hr hh herr hprog (by rw [hpc, ho])
    (by rw [hpc]; exact siteAt_f hF (by omega) (by rw [← ho]; exact insnAt_of_line (fnOk_f hF) hj))
    hP (by rw [hpc]; exact plain_f ho16)

omit hF in
theorem stack_notReloc : ∀ k < 16, ¬ RelocAt I (sp0 - 16#64 + BitVec.ofNat 64 k) := by
  intro k hk hR
  have := (code.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hR).1
  rw [show sp0 - 16#64 = BitVec.ofNat 64 (2 ^ 40 - 16) from rfl, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
  omega

/-- **The facts of the model's run of the entry**: its states before the return meet `StepOk`
and call nothing, and it returns at the fifth step. -/
theorem run_facts (hc : Entry c) (B : BaseEnv) (Mx : Nat) :
    (∀ k ≤ 4, StepOk I B file Mx f (runX ((sys I B).mach Mx f) k c) ∧
      ∀ h, ¬ CallsAt I B f (runX ((sys I B).mach Mx f) k c) h) ∧
    runX ((sys I B).mach Mx f) 5 c = S5 c := by
  have hFf := fnOk_f hF
  obtain ⟨⟨t1, hj1⟩, ⟨t2, hj2⟩, ⟨t4, hj4⟩, ⟨t5, hj5⟩, ⟨t6, hj6⟩, ho1, ho2, ho4, ho5, ho6, -⟩ := code
  obtain ⟨pc0, pc1, pc2, pc3, pc4⟩ := pc_S hc
  obtain ⟨e1, e2, e3, e4, -⟩ := err_S hc
  obtain ⟨p1, p2, p3, p4, -⟩ := prog_S (c := c)
  obtain ⟨sp1, -, sp3, -⟩ := sp_S (c := c)
  have al0 : (spOf c).toNat % 16 = 0 := by rw [hc.sp]; rfl
  have al3 : (spOf (S3 c)).toNat % 16 = 0 := by rw [sp3, hc.sp]; rfl
  have step1 : (sys I B).mach Mx f c = S1 c :=
    mach_line hFf hj1 rfl hc.prog hc.err (by rw [ho1]; exact pc0) fun env => by
      obtain ⟨a, ha, he⟩ := exec_stp_fplr env c ((checkSP_iff c).2 al0); exact ⟨a, ha, he⟩
  have step2 : (sys I B).mach Mx f (S1 c) = S2 c :=
    mach_line hFf hj2 rfl (p1.trans hc.prog) e1 (by rw [ho2]; exact pc1) fun env =>
      exec_mov_fp_sp env (S1 c)
  have step3 : (sys I B).mach Mx f (S2 c) = S3 c :=
    mach_line hFf hj4 rfl (p2.trans hc.prog) e2 (by rw [ho4]; exact pc2) fun env =>
      exec_add_w0 env (S2 c)
  have step4 : (sys I B).mach Mx f (S3 c) = S4 c :=
    mach_line hFf hj5 rfl (p3.trans hc.prog) e3 (by rw [ho5]; exact pc3) fun env =>
      exec_ldp_fplr env (S3 c) ((checkSP_iff _).2 al3)
  have step5 : (sys I B).mach Mx f (S4 c) = S5 c :=
    mach_line hFf hj6 rfl (p4.trans hc.prog) e4 (by rw [ho6]; exact pc4) fun env =>
      exec_ret env (S4 c)
  have r1 : runX ((sys I B).mach Mx f) 1 c = S1 c := by rw [runX_succ']; exact step1
  have r2 : runX ((sys I B).mach Mx f) 2 c = S2 c := by rw [runX_succ', r1]; exact step2
  have r3 : runX ((sys I B).mach Mx f) 3 c = S3 c := by rw [runX_succ', r2]; exact step3
  have r4 : runX ((sys I B).mach Mx f) 4 c = S4 c := by rw [runX_succ', r3]; exact step4
  refine ⟨fun k hk => ?_, by rw [runX_succ', r4]; exact step5⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact ⟨stepOk_at hF hj1 ho1 (by omega) rfl rfl hc.err hc.prog pc0
      (fun _ _ ha e hs => sim_stp ha al0 hs),
      noCall_plain hFf hj1 rfl hc.prog (by rw [ho1]; exact pc0)⟩
  · rw [r1]
    exact ⟨stepOk_at hF hj2 ho2 (by omega) rfl rfl e1 (p1.trans hc.prog) pc1
      (fun _ _ ha e hs => sim_mov ha hs),
      noCall_plain hFf hj2 rfl (p1.trans hc.prog) (by rw [ho2]; exact pc1)⟩
  · rw [r2]
    exact ⟨stepOk_at hF hj4 ho4 (by omega) rfl rfl e2 (p2.trans hc.prog) pc2
      (fun _ _ ha e hs => sim_add ha hs),
      noCall_plain hFf hj4 rfl (p2.trans hc.prog) (by rw [ho4]; exact pc2)⟩
  · rw [r3]
    exact ⟨stepOk_at hF hj5 ho5 (by omega) rfl rfl e3 (p3.trans hc.prog) pc3
      (fun _ _ ha e hs => sim_ldp ha al3 (by rw [sp3, hc.sp]; exact stack_notReloc) hs),
      noCall_plain hFf hj5 rfl (p3.trans hc.prog) (by rw [ho5]; exact pc3)⟩
  · rw [r4]
    exact ⟨stepOk_at hF hj6 ho6 (by omega) rfl rfl e4 (p4.trans hc.prog) pc4
      (fun _ _ ha e hs => sim_ret ha hs),
      noCall_plain hFf hj6 rfl (p4.trans hc.prog) (by rw [ho6]; exact pc4)⟩

/-- **`RunOk` of the entry's run**, at every depth and for every base environment. -/
theorem runOk_entry (hc : Entry c) (B : BaseEnv) (Mx : Nat) : RunOk I B file Mx f c := by
  have hk : ∀ Mx' k, (∀ j ≤ k, ¬ Returned (art I f) c (runX ((sys I B).mach Mx' f) j c)) →
      k ≤ 4 := fun Mx' k hnr => Nat.le_of_not_lt fun hk =>
    hnr 5 (by omega) (by rw [(run_facts hF hc B Mx').2]; exact returned_S5 hc)
  intro M' g t hR
  cases hR with
  | act hnr => exact ((run_facts hF hc B _).1 _ (hk _ _ hnr)).1
  | nest hnr hcall _ => exact absurd hcall (((run_facts hF hc B _).1 _ (hk _ _ hnr)).2 _)

end Run

theorem fnOk_all (file : ByteArray) (hfile : Elf.Agrees file Crates.AArithAbort.exAll) :
    ∀ g ∈ (prog I).funcs, FnOk I file g := fun _ hg =>
  fnOk Crates.AArithAbort.okB_input (Crates.AArithAbort.bin_ok file hfile)
    (okB_sound Crates.AArithAbort.okB_input (Crates.AArithAbort.base_closed (img I)) (fun _ h => h)) hg

theorem entry_model (m : Arm.Memory) : Entry (modelOf I f (r m)) where
  prog := by simp only [modelOf, program_set_program]
  err := by rw [r_modelOf]; exact err_r m
  pc := by rw [r_modelOf]; exact pc_r m
  sp := by
    show Arm.r (.GPR 31#5) (modelOf I f (r m)) = sp0
    rw [r_modelOf]; exact spv_r m

/-- **Non-vacuity of `binary_correct_exec`** (L3) on the `a_arith` executable (panic=abort): for
every file holding the proof's excerpts of the executable (one exists, `agrees_fileOf`; the
executable is one), the machine state whose memory is the file's loaded image, in which outside
code calls its Lean-compiled `core::num::<i32>::wrapping_add` with `2` and `3`, meets every
premise — the binary checks (`Crates.AArithAbort.bin_ok`, `okB_input`), the base environment
(`base_closed`), the stack condition (`acyclic`), the loader premise, the boundary contract, the
reference CLIF run (which returns `5`), `TrapsExplicit`, and the per-state facts `RunOk` of the
model's run — and the theorem gives the **executable machine** (`step`: the processor on the
file's own words) returning to the caller with `5` in x0. -/
theorem binary_correct_exec_witness :
    (∃ file, Elf.Agrees file Crates.AArithAbort.exAll) ∧
    ∀ file, Elf.Agrees file Crates.AArithAbort.exAll →
      (imageOf file).Intact (r (memOf file)) ∧
      OutsideCall I (BinCheck.roByte I Crates.AArithAbort.dataObjs) f (StackBound.stackFn I f)
        (r (memOf file)) args cs.mem ∧
      ClifRun I closedBase f (r (memOf file)) args cs ∧
      TrapsExplicit (Clif.linkEnvN (prog I) closedBase.env M) ((prog I).only f) cs ∧
      RunOk I closedBase file M f (modelOf I f (r (memOf file))) ∧
      Clif.runLoop closedBase.env (prog I) (M + 1) cs =
        .returned [⟨.i32, 5#32⟩] (LinkWitness.retMem run) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step I closedBase file) k (r (memOf file))) ∧
        XHolds ⟨.i32, 5#32⟩ (xreg 0 (runX (step I closedBase file) k (r (memOf file)))) := by
  refine ⟨⟨_, agrees_fileOf⟩, fun file hfile => ?_⟩
  have hf := facts.1
  have hfm := (Clif.Program.func?_some hf).1
  obtain ⟨hX, hoc, -⟩ := binary_witness.2 file hfile
  have hL := okB_sound Crates.AArithAbort.okB_input (Crates.AArithAbort.base_closed (img I))
    (fun _ h => h)
  have htr := trapsExplicit_of_run hL hfm clifEntry rfl run_eq
  have hrun := runOk_entry (fnOk_all file hfile) (entry_model (memOf file)) closedBase M
  have h := binary_correct_exec Crates.AArithAbort.okB_input (Crates.AArithAbort.bin_ok file hfile)
    closedBase (Crates.AArithAbort.base_closed _) hf acyclic M hX hoc (clifRun _) htr hrun
  rw [show Clif.runLoop closedBase.env (prog I) (M + 1) cs = run from rfl, run_eq, x30_r] at h
  obtain ⟨k, hret, hx, -⟩ := h
  exact ⟨hX, hoc, clifRun _, htr, hrun, run_eq, k, hret, hx 0 _ rfl⟩

end Crates.BinaryExecWitness
