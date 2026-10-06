import FV.Arm.Exec

/-! # Frame property of the instruction semantics (L3 (c), D2)

`SimR R m e`: the state `e` has the registers (incl. pc, flags, error) of `m`, and its bytes
outside the set `R` (the program field is not compared). `exec_simR`: **for every decoded
instruction `a`, `SimR R` is preserved by `exec_inst a`, provided the instruction's memory reads
at `m` (`MemReads a m`, a list of byte ranges `(address, length)`) avoid `R`**. Only the loads
read memory: single-register loads (every addressing mode, GPR and SIMD&FP, incl. the
register-offset form and the relocated `ldr` of a GOT pair), `ldp`, and the exclusive /
acquire loads; every other instruction (stores included) needs no side condition.

`E2E.ExecBytes.exec_sim` (`ExecFrameSim.lean`) is the instance `R = RelocAt I`, i.e.
`ExecBytes.Sim`.

Proof: the instruction semantics (`FV/Arm/Insts`) only reach the state through `r`/`w`,
`read_mem_bytes`/`write_mem_bytes`. `sim_norm` unfolds the semantics into these and rewrites
every register read of `e` into the read of `m`; `sim_struct` then walks the state term: a write
(`w`, `write_mem_bytes`) of equal values preserves `SimR` (`simR_w'`, `simR_write_mem_bytes`), a
case split (`if`, `dite`, `match`) splits both sides alike, and a memory read of `e` is the read
of `m` when its range avoids `R` (`rmb_simR`, from the load's `MemReads` hypothesis).
-/

namespace E2E.ExecFrame

open Arm

/-! ## The relation and its structural lemmas -/

/-- `e` simulates `m` outside `R`: the same registers (incl. pc, flags, error), the same bytes
outside `R`. -/
def SimR (R : BitVec 64 → Prop) (m e : ArmState) : Prop :=
  (∀ fld, r fld e = r fld m) ∧ ∀ a, ¬ R a → e.mem a = m.mem a

/-- The byte ranges `(address, length)` avoid `R`. -/
def Avoids (R : BitVec 64 → Prop) (rs : List (BitVec 64 × Nat)) : Prop :=
  ∀ p ∈ rs, ∀ k < p.2, ¬ R (p.1 + BitVec.ofNat 64 k)

variable {R : BitVec 64 → Prop}

theorem simR_w {m e : ArmState} (h : SimR R m e) (fld : StateField) (v : state_value fld) :
    SimR R (w fld v m) (w fld v e) := by
  refine ⟨fun f => ?_, fun a ha => ?_⟩
  · by_cases hf : f = fld
    · subst hf; rw [r_of_w_same, r_of_w_same]
    · rw [r_of_w_different hf, r_of_w_different hf]; exact h.1 f
  · rw [ArmState.mem_w_eq_mem, ArmState.mem_w_eq_mem]; exact h.2 a ha

theorem simR_w' {m e : ArmState} {fld : StateField} {v v' : state_value fld} (hv : v' = v)
    (h : SimR R m e) : SimR R (w fld v m) (w fld v' e) := hv ▸ simR_w h fld v

theorem simR_write_mem {m e : ArmState} (h : SimR R m e) (a : BitVec 64) (b : BitVec 8) :
    SimR R (write_mem a b m) (write_mem a b e) := by
  refine ⟨fun fld => by rw [r_of_write_mem, r_of_write_mem]; exact h.1 fld, fun x hx => ?_⟩
  simp only [write_mem, write_store]
  split
  · rfl
  · exact h.2 x hx

theorem simR_write_mem_bytes : ∀ (k : Nat) (a : BitVec 64) (v : BitVec (k * 8)) {m e : ArmState},
    SimR R m e → SimR R (write_mem_bytes k a v m) (write_mem_bytes k a v e)
  | 0, _, _, _, _, h => h
  | k + 1, _, _, _, _, h => by
    simp only [write_mem_bytes]
    exact simR_write_mem_bytes k _ _ (simR_write_mem h _ _)

theorem simR_ite {c : Prop} [Decidable c] {a a' b b' : ArmState} (h1 : c → SimR R a a')
    (h2 : ¬ c → SimR R b b') : SimR R (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1 hc
  · simp only [hc, ↓reduceIte]; exact h2 hc

theorem simR_dite {c : Prop} [Decidable c] {a a' : c → ArmState} {b b' : ¬ c → ArmState}
    (h1 : ∀ hc, SimR R (a hc) (a' hc)) (h2 : ∀ hc, SimR R (b hc) (b' hc)) :
    SimR R (dite c a b) (dite c a' b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceDIte]; exact h1 hc
  · simp only [hc, ↓reduceDIte]; exact h2 hc

/-- A memory read of `e` in a range avoiding `R` is the read of `m`. -/
theorem rmb_simR {m e : ArmState} (h : SimR R m e) :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, ¬ R (a + BitVec.ofNat 64 k)) →
      read_mem_bytes n a e = read_mem_bytes n a m
  | 0, _, _ => rfl
  | n + 1, a, hR => by
    have h0 : e.mem a = m.mem a := h.2 a (by simpa using hR 0 (by omega))
    have ih := rmb_simR h n (a + 1#64) fun k hk => by
      have := hR (k + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1#64 + BitVec.ofNat 64 k by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega] at this
    simp only [read_mem_bytes, read_mem, read_store, ih, h0]

/-! ## The tactics -/

/-- Unfold the semantics into `r`/`w`/`read_mem_bytes`/`write_mem_bytes` and read the registers
of `e` as those of `m` (`h : SimR R m e`). -/
syntax "sim_norm" ident (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sim_norm $h $[$loc]?) => `(tactic| simp only [exec_inst, state_simp_rules,
      ($h).1, ne_eq, reduceCtorEq, not_false_eq_true,
      r_of_w_different, r_of_write_mem_bytes, CheckSPAlignment, Bool.false_eq_true, true_and,
      and_true, false_and, and_false, not_true_eq_false, ↓reduceIte, ↓reduceDIte,
      Bool.not_eq_true, Bool.not_eq_false, Bool.not_false, Bool.not_true, true_implies] $[$loc]?)

/-- Walk the state terms of `SimR R (F m) (F e)` (after `sim_norm`). `rd : c → ∀ k < n, ¬ R (a +
k)` discharges the memory read `read_mem_bytes n a` of `e` under the branch condition `c`. -/
syntax "sim_struct" ident ("using" term)? : tactic
macro_rules
  | `(tactic| sim_struct $h) => `(tactic| sim_struct $h using trivial)
  | `(tactic| sim_struct $h using $rd) => `(tactic| repeat (first
      | exact $h
      | contradiction
      | (refine simR_w' (by first
          | rfl
          | sim_norm $h
          | ((try sim_norm $h); rw [rmb_simR $h]; (apply $rd) <;> assumption)) ?_)
      | apply simR_write_mem_bytes
      | (apply simR_ite <;> intro _)
      | (apply simR_dite <;> intro _)
      | (split <;>
          (try (rename_i hD; first | rw [show _ = none from hD] | rw [show _ = some _ from hD])) <;>
          (try sim_norm $h))))

macro "sim_auto" h:ident : tactic => `(tactic| (sim_norm $h; sim_struct $h))

/-! ## The memory reads of an instruction -/

namespace RegImm

open LDST

/-- `exec_reg_imm_common`'s `scale`. -/
def scale (i : Reg_imm_cls) : Nat :=
  if i.SIMD? then ((BitVec.lsb i.opc 1) ++ i.size).toNat else i.size.toNat

/-- `exec_reg_imm_common`'s `memop` (`0`: store). -/
def memop (i : Reg_imm_cls) : BitVec 1 :=
  if ¬ i.SIMD? ∧ BitVec.lsb i.opc 1 = 1#1 then 1#1 else BitVec.lsb i.opc 0

/-- `reg_imm_operation`'s address. -/
def addr (i : Reg_imm_cls) (s : ArmState) : BitVec 64 :=
  if i.postindex then read_gpr 64 i.Rn s else read_gpr 64 i.Rn s + i.imm.value (scale i) s

/-- The bytes a single-register load reads. -/
def reads (i : Reg_imm_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if memop i ≠ 0#1 then [(addr i s, (8 <<< scale i) / 8)] else []

def ofUnsigned (i : Reg_unsigned_imm_cls) : Reg_imm_cls :=
  { size := i.size, opc := i.opc, Rn := i.Rn, Rt := i.Rt, SIMD? := i.V = 1#1, wback := false,
    postindex := false, imm := .uimm12 i.imm12 }

def ofPost (i : Reg_imm_post_indexed_cls) : Reg_imm_cls :=
  { size := i.size, opc := i.opc, Rn := i.Rn, Rt := i.Rt, SIMD? := i.V = 1#1, wback := true,
    postindex := true, imm := .simm9 i.imm9 }

def ofPre (i : Reg_imm_pre_indexed_cls) : Reg_imm_cls :=
  { size := i.size, opc := i.opc, Rn := i.Rn, Rt := i.Rt, SIMD? := i.V = 1#1, wback := true,
    postindex := false, imm := .simm9 i.imm9 }

def ofUnscaled (i : Reg_unscaled_imm_cls) : Reg_imm_cls :=
  { size := i.size, opc := i.opc, Rn := i.Rn, Rt := i.Rt, SIMD? := false, wback := false,
    postindex := false, imm := .simm9 i.imm9 }

def ofRegOffset (i : Reg_reg_offset_cls) : Reg_imm_cls :=
  { size := i.size, opc := i.opc, Rn := i.Rn, Rt := i.Rt, SIMD? := false, wback := false,
    postindex := false, imm := .reg i.Rm i.option i.S }

end RegImm

namespace RegPair

open LDST

/-- `exec_reg_pair_common`'s `scale`. -/
def scale (i : Reg_pair_cls) : Nat :=
  if !i.SIMD? then 2 + (BitVec.lsb i.opc 1).toNat else 2 + i.opc.toNat

/-- `reg_pair_operation`'s address. -/
def addr (i : Reg_pair_cls) (s : ArmState) : BitVec 64 :=
  if i.postindex then read_gpr 64 i.Rn s
  else read_gpr 64 i.Rn s + (BitVec.signExtend 64 i.imm7 <<< scale i)

/-- The bytes an `ldp` reads. -/
def reads (i : Reg_pair_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if i.L? then [(addr i s, 2 * ((8 <<< scale i) / 8))] else []

def mk (wback postindex : Bool) (opc : BitVec 2) (V L : BitVec 1) (imm7 : BitVec 7)
    (Rt2 Rn Rt : BitVec 5) : Reg_pair_cls :=
  { opc := opc, SIMD? := V = 1#1, L? := L = 1#1, wback := wback, postindex := postindex,
    imm7 := imm7, Rt2 := Rt2, Rn := Rn, Rt := Rt }

end RegPair

/-- The bytes a SIMD&FP `ldur` reads (`exec_ldstur`). -/
def ldsturReads (i : Reg_unscaled_imm_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if BitVec.getLsbD i.opc 0 then
    [(read_gpr 64 i.Rn s + BitVec.signExtend 64 i.imm9,
      (8 <<< (BitVec.extractLsb' 1 1 i.opc ++ i.size).toNat) / 8)]
  else []

/-- The bytes an exclusive / acquire load reads (`exec_reg_exclusive`). -/
def exclReads (i : Reg_exclusive_cls) (s : ArmState) : List (BitVec 64 × Nat) :=
  if i.L = 1#1 then [(read_gpr 64 i.Rn s, (8 <<< i.size.toNat) / 8)] else []

end E2E.ExecFrame

namespace E2E.ExecBytes

open Arm E2E.ExecFrame

/-- **The byte ranges `(address, length)` the instruction `a` reads at `s`**: the loads' (every
single-register addressing mode, `ldp`, the exclusive / acquire loads); empty for every other
instruction. -/
def MemReads : ArmInst → ArmState → List (BitVec 64 × Nat)
  | .LDST (.Reg_imm_post_indexed i), s => RegImm.reads (RegImm.ofPost i) s
  | .LDST (.Reg_unsigned_imm i), s => RegImm.reads (RegImm.ofUnsigned i) s
  | .LDST (.Reg_unscaled_imm i), s =>
    if i.VR = 0b1#1 then ldsturReads i s else RegImm.reads (RegImm.ofUnscaled i) s
  | .LDST (.Reg_pair_pre_indexed i), s =>
    RegPair.reads (RegPair.mk true false i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_pair_post_indexed i), s =>
    RegPair.reads (RegPair.mk true true i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_pair_signed_offset i), s =>
    RegPair.reads (RegPair.mk false false i.opc i.V i.L i.imm7 i.Rt2 i.Rn i.Rt) s
  | .LDST (.Reg_imm_pre_indexed i), s => RegImm.reads (RegImm.ofPre i) s
  | .LDST (.Reg_reg_offset i), s => RegImm.reads (RegImm.ofRegOffset i) s
  | .LDST (.Reg_exclusive i), s => exclReads i s
  | _, _ => []

end E2E.ExecBytes

namespace E2E.ExecFrame

open Arm E2E.ExecBytes

/-! ## The instruction classes -/

section Classes

variable {m e : ArmState} (h : SimR R m e)
include h

theorem simR_dpi (i : DataProcImmInst) :
    SimR R (exec_inst (.DPI i) m) (exec_inst (.DPI i) e) := by
  cases i <;> sim_auto h

theorem simR_br (i : BranchInst) : SimR R (exec_inst (.BR i) m) (exec_inst (.BR i) e) := by
  cases i <;> sim_auto h

theorem simR_dpr (i : DataProcRegInst) :
    SimR R (exec_inst (.DPR i) m) (exec_inst (.DPR i) e) := by
  cases i <;> sim_auto h

theorem simR_dpsfp (i : DataProcSFPInst) :
    SimR R (exec_inst (.DPSFP i) m) (exec_inst (.DPSFP i) e) := by
  cases i <;> sim_auto h

theorem simR_res (i : ReservedInst) : SimR R (exec_inst (.RES i) m) (exec_inst (.RES i) e) := by
  cases i <;> sim_auto h

theorem simR_reg_imm_common (i : LDST.Reg_imm_cls) (str : String)
    (hR : Avoids R (RegImm.reads i m)) :
    SimR R (LDST.exec_reg_imm_common i str m) (LDST.exec_reg_imm_common i str e) := by
  have hR' : RegImm.memop i ≠ 0#1 → ∀ k < (8 <<< RegImm.scale i) / 8,
      ¬ R (RegImm.addr i m + BitVec.ofNat 64 k) := fun hl =>
    hR (RegImm.addr i m, (8 <<< RegImm.scale i) / 8) (by
      simp only [RegImm.reads, hl, ne_eq, not_false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false])
  simp only [RegImm.memop, RegImm.addr, RegImm.scale] at hR'
  obtain ⟨size, opc, Rn, Rt, SIMD?, wback, postindex, imm⟩ := i
  cases SIMD? <;> cases wback <;> cases postindex <;> cases imm <;>
  · sim_norm h at hR'
    sim_norm h
    sim_struct h using hR'

theorem simR_reg_pair_common (i : LDST.Reg_pair_cls) (str : String)
    (hR : Avoids R (RegPair.reads i m)) :
    SimR R (LDST.exec_reg_pair_common i str m) (LDST.exec_reg_pair_common i str e) := by
  have hR' : i.L? = true → ∀ k < 2 * ((8 <<< RegPair.scale i) / 8),
      ¬ R (RegPair.addr i m + BitVec.ofNat 64 k) := fun hl =>
    hR (RegPair.addr i m, 2 * ((8 <<< RegPair.scale i) / 8)) (by
      simp only [RegPair.reads, hl, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false])
  simp only [RegPair.addr, RegPair.scale] at hR'
  obtain ⟨opc, SIMD?, L?, wback, postindex, imm7, Rt2, Rn, Rt⟩ := i
  cases SIMD? <;> cases L? <;> cases wback <;> cases postindex <;>
  · sim_norm h at hR'
    sim_norm h
    sim_struct h using hR'

theorem simR_ldstur (i : Reg_unscaled_imm_cls) (hR : Avoids R (ldsturReads i m)) :
    SimR R (LDST.exec_ldstur i m) (LDST.exec_ldstur i e) := by
  have hR' : BitVec.getLsbD i.opc 0 = true →
      ∀ k < (8 <<< (BitVec.extractLsb' 1 1 i.opc ++ i.size).toNat) / 8,
      ¬ R (read_gpr 64 i.Rn m + BitVec.signExtend 64 i.imm9 + BitVec.ofNat 64 k) := fun hl =>
    hR (read_gpr 64 i.Rn m + BitVec.signExtend 64 i.imm9,
      (8 <<< (BitVec.extractLsb' 1 1 i.opc ++ i.size).toNat) / 8) (by simp only [ldsturReads, hl, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false])
  sim_norm h at hR'
  sim_norm h
  sim_struct h using hR'

theorem simR_exclusive (i : Reg_exclusive_cls) (hR : Avoids R (exclReads i m)) :
    SimR R (LDST.exec_reg_exclusive i m) (LDST.exec_reg_exclusive i e) := by
  have hR' : i.L = 1#1 → ∀ k < (8 <<< i.size.toNat) / 8,
      ¬ R (read_gpr 64 i.Rn m + BitVec.ofNat 64 k) := fun hl =>
    hR (read_gpr 64 i.Rn m, (8 <<< i.size.toNat) / 8) (by simp only [exclReads, hl, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false])
  sim_norm h at hR'
  sim_norm h
  sim_struct h using hR'

theorem simR_ldst (i : LDSTInst) (hR : Avoids R (MemReads (.LDST i) m)) :
    SimR R (exec_inst (.LDST i) m) (exec_inst (.LDST i) e) := by
  cases i with
  | Reg_imm_post_indexed i => exact simR_reg_imm_common h _ _ hR
  | Reg_unsigned_imm i => exact simR_reg_imm_common h _ _ hR
  | Reg_imm_pre_indexed i => exact simR_reg_imm_common h _ _ hR
  | Reg_reg_offset i =>
    simp only [exec_inst, LDST.exec_reg_reg_offset]
    apply simR_ite (fun _ => simR_w h _ _) fun _ => simR_ite (fun _ => simR_w h _ _) fun _ => ?_
    exact simR_reg_imm_common h _ _ hR
  | Reg_unscaled_imm i =>
    simp only [MemReads] at hR
    simp only [exec_inst, LDST.exec_reg_unscaled_imm]
    split
    · rename_i hv; simp only [hv, ↓reduceIte] at hR; exact simR_ldstur h i hR
    · rename_i hv; simp only [hv, ↓reduceIte] at hR; exact simR_reg_imm_common h _ _ hR
  | Reg_pair_pre_indexed i => exact simR_reg_pair_common h _ _ hR
  | Reg_pair_post_indexed i => exact simR_reg_pair_common h _ _ hR
  | Reg_pair_signed_offset i => exact simR_reg_pair_common h _ _ hR
  | Reg_exclusive i => exact simR_exclusive h i hR

end Classes

/-- **Frame property of the instruction semantics**: if `e` simulates `m` outside `R` and the
memory reads of `a` at `m` avoid `R`, then `e` still simulates `m` after `a`. -/
theorem exec_simR {m e : ArmState} (a : ArmInst) (h : SimR R m e)
    (hR : Avoids R (MemReads a m)) : SimR R (exec_inst a m) (exec_inst a e) := by
  cases a with
  | DPI i => exact simR_dpi h i
  | BR i => exact simR_br h i
  | DPR i => exact simR_dpr h i
  | DPSFP i => exact simR_dpsfp h i
  | LDST i => exact simR_ldst h i hR
  | RES i => exact simR_res h i

end E2E.ExecFrame
