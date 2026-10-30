import FV.Arm.State
import FV.Arm.Insts.Common
import FV.Arm.Insts.DPI.Add_sub_imm
import FV.Arm.Insts.DPI.PC_rel_addressing
import FV.Arm.Insts.DPI.Logical_imm
import FV.Arm.Insts.DPI.Bitfield
import FV.Arm.Insts.DPI.Move_wide_imm
import FV.Arm.Insts.DPI.Extract
import FV.Arm.Insts.DPR.Add_sub_carry
import FV.Arm.Insts.DPR.Add_sub_shifted_reg
import FV.Arm.Insts.DPR.Conditional_select
import FV.Arm.Insts.DPR.Data_processing_one_source
import FV.Arm.Insts.DPR.Data_processing_two_source
import FV.Arm.Insts.DPR.Logical_shifted_reg
import FV.Arm.Insts.DPR.Data_processing_three_source
import FV.Arm.Insts.DPR.Add_sub_ext_reg
import FV.Arm.Insts.DPR.Conditional_compare
import FV.Arm.Insts.BR.Compare_branch
import FV.Arm.Insts.BR.Uncond_branch_imm
import FV.Arm.Insts.BR.Uncond_branch_reg
import FV.Arm.Insts.BR.Cond_branch_imm
import FV.Arm.Insts.BR.Hints
import FV.Arm.Insts.BR.Barrier
import FV.Arm.Insts.BR.Test_branch
import FV.Arm.Insts.BR.Mrs
import FV.Arm.Insts.DPSFP.Advanced_simd_copy
import FV.Arm.Insts.DPSFP.Advanced_simd_two_reg_misc
import FV.Arm.Insts.DPSFP.Advanced_simd_three_same
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source
import FV.Arm.Insts.DPSFP.Conversion_between_FP_and_Int
import FV.Arm.Insts.DPSFP.Advanced_simd_across_lanes
import FV.Arm.Insts.DPSFP.Advanced_simd_modified_immediate
import FV.Arm.Insts.DPSFP.FP_immediate
import FV.Arm.Insts.DPSFP.FP_conditional_select
import FV.Arm.Insts.DPSFP.FP_data_processing_two_source
import FV.Arm.Insts.DPSFP.FP_data_processing_three_source
import FV.Arm.Insts.DPSFP.FP_compare
import FV.Arm.Insts.LDST.Reg_imm
import FV.Arm.Insts.LDST.Reg_unscaled_imm
import FV.Arm.Insts.LDST.Reg_pair
import FV.Arm.Insts.LDST.Reg_literal
import FV.Arm.Insts.Reserved.Udf
import FV.Arm.Memory.MemoryProofs
import FV.Unw.Model
import FV.Backend.Proof.UnwindTables

/-!
# Unwinding through the backend's frames (S10c + S10d, #230/#231)

The emitted tables (`FV/Backend/Proof/UnwindTables.lean`) read by the outside contract
(`FV/Unw/Model.lean`):

* `frameAt_frameRow`: the frame invariant of the backend's frame row (`frameRow fs saved`)
  from the facts the code keeps at its calls (sp + fs + 16 = entry sp, entry x29/x30 at CFA − 16/− 8,
  callee-save slots hold the entry values, other callee-saved registers unchanged).
* `unwind_call_restores`: for a function with a frame, at every call (return offset − 1) the
  row decoded from the emitted FDE bytes restores the ABI return state (`ArmRet`) from a frame
  satisfying `FrameSaved`.
* `personality_callSite`, `personality_plain`: the personality's decision at each call from
  the emitted call-site table (`CallSitesOk`): continue at a plain call, install the first
  handler's landing pad at a `try_call`.
* `scanLines_labelOffsets`, `scanLines_rets_eq`: the landing-pad and return offsets the
  tables are written from are the layout's (`labelOffsets`, `lineOffset` of the call lines,
  `callIdx`), the addresses `insnAt`/`CallPc` and the register-level proofs use.
* Non-vacuity: `Witness.restores` (a concrete frame unwinds to the ABI return).
-/
namespace Unw

open Backend Backend.Proof Backend.Proof.UnwindTables E2E

/-- The value of DWARF register `d` in `s` as the unwinder restores it: x0–x30 and sp, the low
64 bits of v0–v31. -/
def dwarfVal (s : Arm.ArmState) (d : Nat) : BitVec 64 :=
  if d < 32 then xreg d s
  else if 64 ≤ d ∧ d < 96 then (Arm.r (.SFP (BitVec.ofNat 5 (d - 64))) s).setWidth 64
  else 0

theorem frameRow_rule (saved : List (Nat × Int)) (n : Nat) :
    (frameRow saved).rule n =
      (saved.reverse.lookup n).or (if n = 30 then some (-8) else if n = 29 then some (-16) else none) := by
  simp only [Row.rule, frameRow, List.lookup_append]
  congr 1
  simp only [List.lookup_cons, List.lookup_nil]
  by_cases h30 : n = 30
  · subst h30; rfl
  · by_cases h29 : n = 29
    · subst h29; rfl
    · rw [if_neg h30, if_neg h29, show (n == 30) = false by simpa using h30,
        show (n == 29) = false by simpa using h29]

/-- **The frame invariant of the backend's frame row** (Cranelift's, CFA = x29 + 16) from the
facts the compiled code keeps at its calls: x29 + 16 = entry sp (the body keeps x29); the entry
x29 and x30 at CFA − 16 and CFA − 8; each pushed register's slot of `saved` holds its entry
value; every callee-saved register without a slot keeps its entry value. -/
theorem frameAt_frameRow {saved : List (Nat × Int)} {s0 t : Arm.ArmState}
    (hfp : xreg 29 t + 16#64 = spv s0)
    (hfpS : ld64 (spv s0 + BitVec.ofInt 64 (-16)) t = xreg 29 s0)
    (hlr : ld64 (spv s0 + BitVec.ofInt 64 (-8)) t = xreg 30 s0)
    (hsv : ∀ d off, saved.reverse.lookup d = some off →
      ld64 (spv s0 + BitVec.ofInt 64 off) t = dwarfVal s0 d)
    (hx : ∀ n ∈ calleeSavedX, n ≠ 29 → saved.reverse.lookup n = none → xreg n t = xreg n s0)
    (hv : ∀ n, 8 ≤ n → n < 16 → saved.reverse.lookup (64 + n) = none →
      (Arm.r (.SFP (BitVec.ofNat 5 n)) t).setWidth 64 = (Arm.r (.SFP (BitVec.ofNat 5 n)) s0).setWidth 64) :
    FrameAt (frameRow saved) s0 t where
  cfa := by
    simp only [Row.cfa?, regVal?, frameRow]
    rw [← hfp]
    rfl
  regs := by
    intro n hn
    have hn32 : n < 31 := by
      simp only [calleeSavedX, List.mem_cons, List.mem_map, List.mem_range] at hn; omega
    unfold restoredX
    rw [frameRow_rule]
    cases hl : saved.reverse.lookup n with
    | some off =>
      simp only [Option.some_or]
      rw [hsv n off hl]
      simp [dwarfVal, show n < 32 by omega]
    | none =>
      simp only [Option.none_or]
      by_cases h30 : n = 30
      · subst h30; simpa using hlr
      · by_cases h29 : n = 29
        · subst h29; simpa using hfpS
        · rw [if_neg h30, if_neg h29]
          have hmem : n ∈ calleeSavedX := by
            rcases List.mem_cons.mp hn with h | h
            · exact absurd h h30
            · exact h
          exact hx n hmem h29 hl
  vregs := by
    intro n h8 h16
    unfold restoredV
    rw [frameRow_rule, if_neg (by omega), if_neg (by omega)]
    cases hl : saved.reverse.lookup (64 + n) with
    | some off =>
      simp only [Option.some_or]
      rw [hsv _ off hl]
      simp only [dwarfVal]
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    | none =>
      simp only [Option.none_or]
      exact hv n h8 h16 hl

/-- The facts `frameAt_frameRow` needs, for the prologue's pushes of `af`, when the activation
was entered in `s0` and is at a call in `t`. -/
def FrameSaved (af : AFunc) (s0 t : Arm.ArmState) : Prop :=
  FrameAt (frameRow ((pushRows af.saves 8).map offsetPair)) s0 t

/-- **The emitted CFI unwinds a frame at every call** (S10c + S10d): for a function with a
frame, the FDE bytes `cfiProgram rows` decode, and at every call's return offset − 1 the
unwinder's row restores the ABI return state from a frame satisfying the frame invariant. -/
theorem unwind_call_restores {af : AFunc} {fa : FnAsm} {rows : List (Nat × Cfi)}
    (h : unwindRows af fa = .ok rows) (hf : af.frame = true)
    {ret : Nat} (hret : ret ∈ (scanLines fa.lines.toList 0 [] []).2)
    {s0 t : Arm.ArmState} (hfr : FrameSaved af s0 t) (herr : Arm.r .ERR t = .None) :
    decodeCfa? (cfiProgram rows).data.toList = some (insnsFrom 0 rows) ∧
    ∃ t', restore (rowAt cieInsns (insnsFrom 0 rows) (ret - 1)) t = some t' ∧
      ArmRet (xreg 30 s0) s0 t' ∧ t'.program = t.program ∧ t'.mem = t.mem := by
  obtain ⟨hok, hrow⟩ := unwindRows_frame h hf
  refine ⟨decodeCfa?_cfiProgram rows hok, ?_⟩
  rw [hrow ret hret]
  exact restore_frame hfr herr

/-! ## The personality at the backend's calls -/

/-- The personality at a call the call-site table `sites` describes (`CallSitesOk`): for a
plain call it continues unwinding; for a `try_call` whose first handler's landing pad is at
`pad ≠ 0` it installs that landing pad. (Since #553 the entry is looked up in the
alias-extended label list, which is what `CallSitesOk`'s `entryFor` uses and what the
conclusion states.) -/
theorem personality_callSite {af : AFunc} {fa : FnAsm} {sites : List CallSite}
    (h : CallSitesOk af fa sites) {c : Option TryInfo} {ret : Nat}
    (hp : (c, ret) ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2) :
    ∃ e, entryFor (fa.alias.filterMap (fun l =>
        ((scanLines fa.lines.toList 0 [] []).1.lookup l.2).map fun x => (l.1, x)) ++
      (scanLines fa.lines.toList 0 [] []).1) (c, ret) = some e ∧
      personality (some (sites.map (·.entry))) (ret - 1) =
        if e.pad = 0 then .continue else .install e.pad := by
  obtain ⟨hs, hl⟩ := h.2 _ hp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨e, he, ?_⟩
  simp only [personality]
  rw [hl, he]

theorem entryFor_plain (labs : List (Label × Nat)) (ret : Nat) :
    entryFor labs (none, ret) = some ⟨ret - 1, 1, 0, 0⟩ := rfl

/-- At a plain call (no handlers) the personality continues unwinding. -/
theorem personality_plain {af : AFunc} {fa : FnAsm} {sites : List CallSite}
    (h : CallSitesOk af fa sites) {ret : Nat}
    (hp : (none, ret) ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2) :
    personality (some (sites.map (·.entry))) (ret - 1) = .continue := by
  obtain ⟨e, he, hpe⟩ := personality_callSite h hp
  rw [entryFor_plain] at he
  cases he
  simpa using hpe


/-! ## Non-vacuity -/

namespace Witness

/-- Any state with sp := 4096. -/
def s0 (s : Arm.ArmState) : Arm.ArmState := Arm.w (.GPR 31#5) 4096#64 s

/-- The frame `t s` of a function with no fixed frame and no pushes entered in `s0 s`, at a
call: entry x29 at 4080, entry x30 at 4088, x29 = sp := 4080. -/
def t (s : Arm.ArmState) : Arm.ArmState :=
  Arm.write_mem_bytes 8 4080#64 (xreg 29 (s0 s))
    (Arm.write_mem_bytes 8 4088#64 (xreg 30 (s0 s))
      (Arm.w (.GPR 29#5) 4080#64 (Arm.w (.GPR 31#5) 4080#64 (s0 s))))

theorem t_gpr (s : Arm.ArmState) (n : Nat) (hn : n < 31) (h29 : n ≠ 29) :
    xreg n (t s) = xreg n (s0 s) := by
  simp only [t, xreg, Arm.r_of_write_mem_bytes]
  rw [Arm.r_of_w_different (by
    simp only [ne_eq, Arm.StateField.GPR.injEq]
    exact ofNat5_ne (b := 29) (by omega) (by omega) h29), Arm.r_of_w_different (by
    simp only [ne_eq, Arm.StateField.GPR.injEq]
    exact ofNat5_ne (b := 31) (by omega) (by omega) (by omega))]

/-- **Non-vacuity of `restore_frame`**: the frame row of a function without pushes unwinds the
frame `t s` to the ABI return of the activation entered in `s0 s`. -/
theorem restores (s : Arm.ArmState) (herr : Arm.r .ERR s = .None) :
    ∃ t', restore (frameRow []) (t s) = some t' ∧ ArmRet (xreg 30 (s0 s)) (s0 s) t' := by
  have hsp : spv (s0 s) = 4096#64 := by simp [spv, s0, Arm.r_of_w_same]
  have hfr : FrameAt (frameRow []) (s0 s) (t s) := by
    apply frameAt_frameRow
    · rw [hsp]
      simp only [t, xreg, Arm.r_of_write_mem_bytes, Arm.r_of_w_same]
      decide
    · rw [hsp, show (4096#64 + BitVec.ofInt 64 (-16)) = 4080#64 by decide]
      simp only [ld64, t]
      exact Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)
    · rw [hsp, show (4096#64 + BitVec.ofInt 64 (-8)) = 4088#64 by decide]
      simp only [ld64, t]
      rw [Arm.read_mem_bytes_of_write_mem_bytes_different (by decide) (by decide) (by decide)]
      exact Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)
    · intro d off h; simp at h
    · intro n hn h29 _
      exact t_gpr s n (by simp only [calleeSavedX, List.mem_map, List.mem_range] at hn; omega) h29
    · intro n _ _ _
      simp only [t, Arm.r_of_write_mem_bytes]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
  have herr' : Arm.r .ERR (t s) = .None := by
    simp only [t, s0, Arm.r_of_write_mem_bytes]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
      Arm.r_of_w_different (by simp), herr]
  obtain ⟨t', hr, hret, -, -⟩ := restore_frame hfr herr'
  exact ⟨t', hr, hret⟩

end Witness

end Unw

/-! ## The tables' offsets are the layout's (`labelOffsets`, `lineOffset`) -/

namespace Backend.Proof.UnwindTables

open Backend

/-- The labels `scanLines` records agree with `labelOffsets` (which defines each label once). -/
theorem scanLines_labs_go : ∀ (L : List Line) (off : Nat) (labs : List (Label × Nat))
    (rets : List Nat) (m lm : Std.HashMap Lbl Nat),
    (∀ l v, labs.lookup l = some v → m[Lbl.block l]? = some v) →
    (∀ l, (labs.lookup l).isNone → m.contains (Lbl.block l) = false) →
    labelOffsets.go L off m = .ok lm →
    ∀ l v, (scanLines L off labs rets).1.lookup l = some v → lm[Lbl.block l]? = some v
  | [], off, labs, rets, m, lm, h1, _, hg, l, v, hl => by
    simp only [labelOffsets.go, pure, Except.pure, Except.ok.injEq] at hg
    subst hg
    exact h1 l v hl
  | ln :: L, off, labs, rets, m, lm, h1, h2, hg, l, v, hl => by
    simp only [scanLines] at hl
    unfold labelOffsets.go at hg
    cases ln with
    | label lb =>
      by_cases hc : m.contains lb = true
      · simp only [hc, ite_true] at hg; cases hg
      · simp only [hc, Bool.false_eq_true, ite_false] at hg
        simp only [Line.size, Nat.add_zero] at hl
        refine scanLines_labs_go L off _ rets _ lm ?_ ?_ hg l v hl
        · intro l' v' hl'
          unfold labsAfter at hl'
          split at hl'
          · rename_i lb' heq
            cases heq
            simp only [List.lookup_cons] at hl'
            by_cases he : l' = lb'
            · subst he
              simp only [beq_self_eq_true] at hl'
              cases hl'
              simp
            · rw [show (l' == lb') = false by simpa using he] at hl'
              rw [Std.HashMap.getElem?_insert]
              rw [if_neg (by simpa using fun h => he (Lbl.block.inj h).symm)]
              exact h1 l' v' hl'
          · rw [Std.HashMap.getElem?_insert]
            split
            · rename_i heq
              exfalso
              have := h1 l' v' hl'
              rw [beq_iff_eq] at heq
              subst heq
              have hcon : m.contains (Lbl.block l') = true := by
                rw [Std.HashMap.contains_eq_isSome_getElem?, this]; rfl
              exact hc hcon
            · exact h1 l' v' hl'
        · intro l' hn
          rw [Std.HashMap.contains_insert]
          unfold labsAfter at hn
          split at hn
          · rename_i lb' heq
            cases heq
            simp only [List.lookup_cons] at hn
            by_cases he : l' = lb'
            · subst he; simp at hn
            · rw [show (l' == lb') = false by simpa using he] at hn
              simp only [Bool.or_eq_false_iff]
              refine ⟨by simpa using fun h => he (Lbl.block.inj h).symm, h2 l' hn⟩
          · simp only [Bool.or_eq_false_iff]
            refine ⟨?_, h2 l' hn⟩
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro h
            subst h
            rename_i hnl
            exact hnl _ rfl
    | ins i t =>
      exact scanLines_labs_go L _ _ _ m lm h1 h2 hg l v hl
    | word a b =>
      exact scanLines_labs_go L _ _ _ m lm h1 h2 hg l v hl

/-- **The landing-pad offsets of the LSDA are the label offsets of the layout**: a label offset
`scanLines` finds (what `callSites` writes as a landing pad) is `labelOffsets`'. -/
theorem scanLines_labelOffsets {fa : FnAsm} {lm : Std.HashMap Lbl Nat}
    (hm : labelOffsets fa.lines = .ok lm) {l : Label} {v : Nat}
    (hl : (scanLines fa.lines.toList 0 [] []).1.lookup l = some v) : lm[Lbl.block l]? = some v :=
  scanLines_labs_go _ 0 [] [] {} lm (by simp) (by simp) hm l v hl


/-- The indices of the call lines (`bl`/`blr`) of `L`, in order. -/
def callIdx : List Line → List Nat
  | [] => []
  | ln :: L => (if ln.isCall then [0] else []) ++ (callIdx L).map (· + 1)

theorem retsAfter_eq (ln : Line) (off : Nat) (rets : List Nat) :
    retsAfter ln off rets = if ln.isCall then (off + 4) :: rets else rets := by
  rcases ln with ⟨i, t⟩ | ⟨a, b⟩ | ⟨l⟩
  · cases i <;> rfl
  · rfl
  · rfl

theorem lineOffset_cons_succ (ln : Line) (L : List Line) (j : Nat) :
    lineOffset (ln :: L) (j + 1) = ln.size + lineOffset L j := by
  simp [lineOffset, List.take_succ_cons]

/-- **The return offsets `scanLines` collects are the calls' layout offsets + 4**, in order:
the `k`-th is that of the `k`-th call line. -/
theorem scanLines_rets_eq : ∀ (L : List Line) (off : Nat) (labs : List (Label × Nat))
    (rets : List Nat), (scanLines L off labs rets).2 =
      rets.reverse ++ (callIdx L).map (fun j => off + lineOffset L j + 4)
  | [], _, _, _ => by simp [scanLines, callIdx]
  | ln :: L, off, labs, rets => by
    simp only [scanLines]
    rw [scanLines_rets_eq L, retsAfter_eq]
    simp only [callIdx, List.map_append, List.map_map]
    have hf : ((fun j => off + lineOffset (ln :: L) j + 4) ∘ (· + 1)) =
        fun j => off + ln.size + lineOffset L j + 4 := by
      funext j
      simp only [Function.comp, lineOffset_cons_succ]
      omega
    rw [hf]
    split
    · simp [lineOffset]
    · simp

/-- Every call line's index is a call line. -/
theorem callIdx_spec : ∀ (L : List Line) (j : Nat), j ∈ callIdx L →
    ∃ ln, L[j]? = some ln ∧ ln.isCall = true
  | [], j, h => by simp [callIdx] at h
  | ln :: L, j, h => by
    simp only [callIdx, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨j', hj', rfl⟩
    · split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨ln, rfl, by assumption⟩
      · simp at h
    · obtain ⟨l, hl, hc⟩ := callIdx_spec L j' hj'
      exact ⟨l, by simpa using hl, hc⟩

end Backend.Proof.UnwindTables
