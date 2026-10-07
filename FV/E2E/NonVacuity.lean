import FV.E2E.Link

/-! # Non-vacuity of the callee contracts (docs/contracts/e2e.md, "Non-vacuity")

The end-to-end theorems (`backend_correct_final`, `_opt_proven`, `_legal`, `_linked`) assume
contracts on the machine's hooks `H` (`CalleeOk`, `TlsOk`) and on the external semantics `X`
(`XCallsOk`, `XCallsIndOk`, `hsym`). This file shows that they can all hold together, for a
callee that pushes a frame below `sp` — the situation in which the former `CalleeOk` (memory
compared outside the caller's frame only) was unsatisfiable (`calleeOk_saves_lr_false`, removed
with it).

* `framed g body`: the callee at `g` as the Arm model runs it: `bl g`, then the backend's frame
  code for an empty frame (`prologueLines 0`: `stp x29, x30, [sp, #-16]!; mov x29, sp`), `body`,
  `epilogueLines 0` (`ldp x29, x30, [sp], #16; ret`), each instruction executed by
  `Arm.exec_inst` of its encoding (`Insn.toArmInst`).
* `KeepsBut K h`: `h` keeps every state field but the pc and x30, the program, and the memory
  outside the `K` bytes below `sp`; `framed_spec`/`keepsBut_framed`: a framed body with budget
  `K` has budget `K + 16`, returns to `pc + 4`, and leaves the caller's return address `pc + 4`
  (and its fp) in the 16 bytes below `sp`.
* `witnessHooks g h`: every call runs `g`, which calls the leaf `h`, both framed (two frames
  pushed below `sp`, `witness_saves_lr`); the TLSDESC hook is the static TLSDESC resolver
  (thread pointer plus the variable's offset), with no stack use.
* `witnessX`: every callee whose name satisfies `idf` returns its first argument, every other one
  returns nothing; the world is unchanged; symbols at `sym`.
* **`calleeOk_witness`**: `CalleeOk F K (witnessX …) (witnessHooks g h) S` for every frame `F`,
  every budget `K ≥ 32` and every set of call sites `S` of the identity shape (`IdShape`: a call
  of an `idf` callee takes its first argument in x0 and defines at most x0; any other call
  defines nothing), in particular for every call site of a function whose callees all return
  nothing.
* **`tlsOk_witness`**, **`xCallsOk_witness`**, **`xCallsIndOk_witness`**: the TLSDESC contract
  and the external contracts for environments whose externs are the identity on their first
  argument (`idf`) or no-ops.
* **`final_contracts_witness`**: all the contract premises of `backend_correct_final` at once;
  **`backend_correct_final_witness`**: the theorem with them discharged.
* Value-returning callees: `idX` (callees `idf` return their first argument), `IdSite idf` (the
  call-site shapes of `(i64) -> i64` calls and of calls without results), `calleeOk_id`,
  `xCallsOk_id`, `final_contracts_id`, **`backend_correct_final_id`**.
* Functions with `try_call`s: `calleeTryOk_witness` (the `try_call` contract at sites whose
  callee returns nothing, for every hook: the payload registers x0/x1 are unconstrained on a
  normal return), **`backend_correct_final_try_witness`**.
-/

namespace E2E

open Backend Backend.Proof

/-! ## Running the frame code -/

/-- One instruction run by the Arm model (its encoding executed). -/
def runIns (i : Insn) (s : Arm.ArmState) : Arm.ArmState :=
  match i.toArmInst env0 with
  | .ok a => Arm.exec_inst a s
  | .error _ => s

/-- `stp x29, x30, [sp, #-16]!` -/
abbrev stpI : Insn := .stp Reg.fp Reg.lr (.spPreIndexed (-16))
/-- `mov x29, sp` -/
abbrev movI : Insn := .mov true Reg.fp .sp
/-- `ldp x29, x30, [sp], #16` -/
abbrev ldpI : Insn := .ldp Reg.fp Reg.lr (.spPostIndexed 16)

theorem prologue0 : prologueLines 0 = [.ins stpI, .ins movI] := by
  rw [prologueLines_eq]; simp [spAdjLines]

theorem epilogue0 : epilogueLines 0 = [.ins ldpI, .ins .ret] := by
  rw [epilogueLines_eq]; simp [spAdjLines]

theorem runIns_stp (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    runIns stpI s = Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.GPR 31#5) (spOf s - 16#64)
        (Arm.write_mem_bytes 16 (spOf s - 16#64) (xreg 30 s ++ xreg 29 s) s)) := by
  obtain ⟨a, ha, he⟩ := exec_stp_fplr env0 s hal
  simp only [runIns, ha, he]

theorem runIns_mov (s : Arm.ArmState) :
    runIns movI s = Arm.w (.GPR 29#5) (spOf s) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
  obtain ⟨a, ha, he⟩ := exec_mov_fp_sp env0 s
  simp only [runIns, ha, he]

theorem runIns_ldp (s : Arm.ArmState) (hal : Arm.CheckSPAlignment s) :
    runIns ldpI s = Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.GPR 31#5) (spOf s + 16#64)
        (Arm.w (.GPR 30#5) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 64 64)
          (Arm.w (.GPR 29#5) ((Arm.read_mem_bytes 16 (spOf s) s).extractLsb' 0 64) s))) := by
  obtain ⟨a, ha, he⟩ := exec_ldp_fplr env0 s hal
  simp only [runIns, ha, he]

theorem runIns_ret (s : Arm.ArmState) : runIns .ret s = Arm.w .PC (xreg 30 s) s := by
  obtain ⟨a, ha, he⟩ := exec_ret env0 s
  simp only [runIns, ha, he]

/-- `bl g`: the return address in x30, the pc at `g`. -/
def blTo (g : BitVec 64) (s : Arm.ArmState) : Arm.ArmState :=
  Arm.w .PC g (Arm.w (.GPR 30#5) (Arm.r .PC s + 4#64) s)

/-- **A framed callee**: `bl g`, then the function at `g` with the backend's frame code for an
empty frame (`prologueLines 0`, `body`, `epilogueLines 0`). -/
def framed (g : BitVec 64) (body : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) :
    Arm.ArmState :=
  runIns .ret (runIns ldpI (body (runIns movI (runIns stpI (blTo g s)))))

/-- The `K` bytes below `sp` in the ring of addresses (`[sp - K, sp)` modulo `2^64`). -/
def BelowMod (K : Nat) (sp a : BitVec 64) : Prop :=
  0 < (sp - a).toNat ∧ (sp - a).toNat ≤ K

theorem stackBelow_of_belowMod {K : Nat} {sp a : BitVec 64} (hK : K ≤ sp.toNat)
    (h : BelowMod K sp a) : StackBelow K sp a := by
  obtain ⟨h1, h2⟩ := h
  have e := BitVec.toNat_sub sp a
  have := a.isLt
  have := sp.isLt
  rw [e] at h1 h2
  by_cases hc : a.toNat < sp.toNat
  · have e' : (2 ^ 64 - a.toNat + sp.toNat) % 2 ^ 64 = sp.toNat - a.toNat := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [e'] at h2
    exact ⟨hc, by omega⟩
  · exfalso
    by_cases h0 : a.toNat = sp.toNat
    · rw [h0, Nat.sub_add_cancel (by omega), Nat.mod_self] at h1; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h2; omega

/-- **What a callee may do with a stack budget of `K` bytes**: from an error-free state with
`sp` aligned, keep every field but the pc and x30, the program, and the memory outside the `K`
bytes below `sp`. -/
def KeepsBut (K : Nat) (h : Arm.ArmState → Arm.ArmState) : Prop :=
  ∀ s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (h s) = Arm.r f s) ∧
    (∀ a, ¬ BelowMod K (spOf s) a → (h s).mem a = s.mem a) ∧ (h s).program = s.program

theorem keepsBut_id : KeepsBut 0 id :=
  fun _ _ _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem align_sub16 {s t : Arm.ArmState} (hal : Arm.CheckSPAlignment s)
    (h : spOf t = spOf s - 16#64) : Arm.CheckSPAlignment t := by
  rw [checkSP_iff, h]
  have := (checkSP_iff s).1 hal
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem align_eq {s t : Arm.ArmState} (hal : Arm.CheckSPAlignment s) (h : spOf t = spOf s) :
    Arm.CheckSPAlignment t := by
  rw [checkSP_iff, h]; exact (checkSP_iff s).1 hal

theorem read_mem_bytes_w {n : Nat} {a : BitVec 64} {f : Arm.StateField} {v} {s : Arm.ArmState} :
    Arm.read_mem_bytes n a (Arm.w f v s) = Arm.read_mem_bytes n a s :=
  read_mem_bytes_congr _ _ fun _ _ => by rw [Arm.ArmState.mem_w_eq_mem]

/-- **The framed callee**, with a body of budget `K`: every field but the pc and x30 kept, the
memory outside the `K + 16` bytes below `sp` kept, the program kept, the return at `pc + 4`,
and the 16 bytes below `sp` holding the return address `pc + 4` and the caller's fp (as
`stp x29, x30` left them). -/
theorem framed_spec {K : Nat} {body : Arm.ArmState → Arm.ArmState} (hb : KeepsBut K body)
    (hK : K + 16 < 2 ^ 64) (g : BitVec 64) (s : Arm.ArmState) (herr : Arm.r .ERR s = .None)
    (hal : Arm.CheckSPAlignment s) :
    (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (framed g body s) = Arm.r f s) ∧
    (∀ a, ¬ BelowMod (K + 16) (spOf s) a → (framed g body s).mem a = s.mem a) ∧
    (framed g body s).program = s.program ∧
    Arm.r .PC (framed g body s) = Arm.r .PC s + 4#64 ∧
    Arm.read_mem_bytes 16 (spOf s - 16#64) (framed g body s) = (Arm.r .PC s + 4#64) ++ xreg 29 s := by
  -- `bl g`
  have hsp0 : spOf (blTo g s) = spOf s := by simp [blTo, spOf, Arm.r_of_w_different]
  have hal0 := align_eq hal hsp0
  have hx30 : xreg 30 (blTo g s) = Arm.r .PC s + 4#64 := by
    simp [blTo, xreg, Arm.r_of_w_different, Arm.r_of_w_same]
  have hx29 : xreg 29 (blTo g s) = xreg 29 s := by
    simp [blTo, xreg, Arm.r_of_w_different]
  -- `stp x29, x30, [sp, #-16]!`
  obtain ⟨s1, hs1e⟩ : ∃ s1, runIns stpI (blTo g s) = s1 := ⟨_, rfl⟩
  have hs1 : s1 = Arm.w .PC (Arm.r .PC (blTo g s) + 4#64) (Arm.w (.GPR 31#5) (spOf s - 16#64)
      (Arm.write_mem_bytes 16 (spOf s - 16#64) ((Arm.r .PC s + 4#64) ++ xreg 29 s) (blTo g s))) := by
    rw [← hs1e, runIns_stp _ hal0, hsp0, hx30, hx29]
  have hsp1 : spOf s1 = spOf s - 16#64 := by
    rw [hs1]; simp [spOf, Arm.r_of_w_different, Arm.r_of_w_same]
  have hal1 := align_sub16 hal hsp1
  have hm1 : ∀ a, s1.mem a = (Arm.write_mem_bytes 16 (spOf s - 16#64)
      ((Arm.r .PC s + 4#64) ++ xreg 29 s) (blTo g s)).mem a := by
    intro a; rw [hs1]; simp only [Arm.ArmState.mem_w_eq_mem]
  -- `mov x29, sp`
  obtain ⟨s2, hs2e⟩ : ∃ s2, runIns movI s1 = s2 := ⟨_, rfl⟩
  have hs2 : s2 = Arm.w (.GPR 29#5) (spOf s1) (Arm.w .PC (Arm.r .PC s1 + 4#64) s1) := by
    rw [← hs2e, runIns_mov]
  have hsp2 : spOf s2 = spOf s - 16#64 := by
    rw [hs2, ← hsp1]; simp [spOf, Arm.r_of_w_different]
  have hm2 : ∀ a, s2.mem a = s1.mem a := by
    intro a; rw [hs2]; simp only [Arm.ArmState.mem_w_eq_mem]
  have herr2 : Arm.r .ERR s2 = .None := by
    rw [hs2, hs1]; simp [Arm.r_of_w_different, Arm.r_of_write_mem_bytes, blTo, herr]
  -- the body
  obtain ⟨hf3, hm3, hp3⟩ := hb s2 herr2 (align_eq hal1 (hsp2.trans hsp1.symm))
  obtain ⟨s3, hs3⟩ : ∃ s3, body s2 = s3 := ⟨_, rfl⟩
  rw [hs3] at hf3 hm3 hp3
  have hsp3 : spOf s3 = spOf s - 16#64 := by
    rw [← hsp2]; exact hf3 _ (by simp) (by simp)
  have hal3 := align_sub16 hal hsp3
  -- the saved pair survives the body
  have hnb : ∀ k < 16, ¬ BelowMod K (spOf s2) (spOf s - 16#64 + BitVec.ofNat 64 k) := by
    intro k hk ⟨h1, h2⟩
    rw [hsp2] at h1 h2
    have e : (spOf s - 16#64 - (spOf s - 16#64 + BitVec.ofNat 64 k)).toNat =
        (2 ^ 64 - k) % 2 ^ 64 := by
      rw [show spOf s - 16#64 - (spOf s - 16#64 + BitVec.ofNat 64 k) = - BitVec.ofNat 64 k by
        bv_omega]
      simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega)]
    rw [e] at h1 h2
    by_cases hk0 : k = 0
    · subst hk0; simp at h1
    · rw [Nat.mod_eq_of_lt (by omega)] at h2; omega
  have hrd : Arm.read_mem_bytes 16 (spOf s - 16#64) s3 = (Arm.r .PC s + 4#64) ++ xreg 29 s := by
    rw [read_mem_bytes_congr 16 _ (fun k hk => ((hm3 _ (hnb k hk)).trans (hm2 _)).trans (hm1 _)),
      Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)]
  -- `ldp x29, x30, [sp], #16`
  obtain ⟨s4, hs4e⟩ : ∃ s4, runIns ldpI s3 = s4 := ⟨_, rfl⟩
  have hs4 : s4 = Arm.w .PC (Arm.r .PC s3 + 4#64) (Arm.w (.GPR 31#5) (spOf s - 16#64 + 16#64)
      (Arm.w (.GPR 30#5) (Arm.r .PC s + 4#64) (Arm.w (.GPR 29#5) (xreg 29 s) s3))) := by
    rw [← hs4e, runIns_ldp _ hal3, hsp3, hrd, BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right]
  have hpc4 : xreg 30 s4 = Arm.r .PC s + 4#64 := by
    rw [hs4]; simp [xreg, Arm.r_of_w_different, Arm.r_of_w_same]
  -- `ret`
  have hfr : framed g body s = Arm.w .PC (Arm.r .PC s + 4#64) s4 := by
    rw [framed, hs1e, hs2e, hs3, hs4e, runIns_ret, hpc4]
  rw [hfr]
  refine ⟨fun f h1 h2 => ?_, fun a ha => ?_, ?_, by simp [Arm.r_of_w_same], ?_⟩
  · rw [Arm.r_of_w_different h1, hs4, Arm.r_of_w_different h1]
    by_cases h31 : f = .GPR 31#5
    · subst h31
      rw [Arm.r_of_w_same]
      exact BitVec.sub_add_cancel _ _
    rw [Arm.r_of_w_different h31, Arm.r_of_w_different h2]
    by_cases h29 : f = .GPR 29#5
    · subst h29
      rw [Arm.r_of_w_same]; rfl
    rw [Arm.r_of_w_different h29, hf3 f h1 h2, hs2, Arm.r_of_w_different h29,
      Arm.r_of_w_different h1, hs1, Arm.r_of_w_different h1, Arm.r_of_w_different h31,
      Arm.r_of_write_mem_bytes]
    simp only [blTo]
    rw [Arm.r_of_w_different h1, Arm.r_of_w_different h2]
  · have hnb2 : ¬ BelowMod K (spOf s2) a := by
      intro ⟨h1, h2⟩
      refine ha ⟨?_, ?_⟩ <;>
      · rw [hsp2] at h1 h2
        have e : spOf s - a = (spOf s - 16#64 - a) + 16#64 := by bv_omega
        rw [e, BitVec.toNat_add]
        simp only [BitVec.toNat_ofNat]
        have := (spOf s - 16#64 - a).isLt
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    have hout : ∀ k < 16, a ≠ spOf s - 16#64 + BitVec.ofNat 64 k := by
      intro k hk e
      subst e
      refine ha ⟨?_, ?_⟩ <;>
      · rw [show spOf s - (spOf s - 16#64 + BitVec.ofNat 64 k) = BitVec.ofNat 64 (16 - k) by
          bv_omega]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    simp only [Arm.ArmState.mem_w_eq_mem]
    rw [hs4]
    simp only [Arm.ArmState.mem_w_eq_mem]
    rw [hm3 a hnb2, hm2, hm1, mem_write_mem_bytes_ne _ _ _ _ _ hout]
    simp [blTo, Arm.ArmState.mem_w_eq_mem]
  · rw [Arm.w_program, hs4]
    simp only [Arm.w_program]
    rw [hp3, hs2, Arm.w_program, Arm.w_program, hs1, Arm.w_program, Arm.w_program,
      Arm.write_mem_bytes_program, blTo, Arm.w_program, Arm.w_program]
  · rw [read_mem_bytes_w, hs4]
    simp only [read_mem_bytes_w]
    exact hrd

/-- A framed body of budget `K` has budget `K + 16`. -/
theorem keepsBut_framed {K : Nat} {body : Arm.ArmState → Arm.ArmState} (hb : KeepsBut K body)
    (hK : K + 16 < 2 ^ 64) (g : BitVec 64) : KeepsBut (K + 16) (framed g body) := by
  intro s herr hal
  obtain ⟨h1, h2, h3, -, -⟩ := framed_spec hb hK g s herr hal
  exact ⟨h1, h2, h3⟩

theorem keepsBut_mono {K K' : Nat} {h : Arm.ArmState → Arm.ArmState} (hb : KeepsBut K h)
    (hKK : K ≤ K') : KeepsBut K' h := by
  intro s herr hal
  obtain ⟨h1, h2, h3⟩ := hb s herr hal
  exact ⟨h1, fun a ha => h2 a fun ⟨b1, b2⟩ => ha ⟨b1, by omega⟩, h3⟩

/-! ## The witness hooks and external semantics -/

/-- **The witness callee**: `bl g`, where `g` calls the leaf `h` (`bl h`); both have the backend's
frame code (`prologueLines 0`, `epilogueLines 0`), so each pushes the return address and fp
below `sp`. -/
def witnessCall (g h : BitVec 64) : Arm.ArmState → Arm.ArmState := framed g (framed h id)

theorem witnessCall_keepsBut (g h : BitVec 64) : KeepsBut 32 (witnessCall g h) :=
  keepsBut_framed (keepsBut_framed keepsBut_id (by decide) h) (by decide) g

theorem witnessCall_pc (g h : BitVec 64) (s : Arm.ArmState) (herr : Arm.r .ERR s = .None)
    (hal : Arm.CheckSPAlignment s) : Arm.r .PC (witnessCall g h s) = Arm.r .PC s + 4#64 :=
  (framed_spec (keepsBut_framed keepsBut_id (by decide) h) (by decide) g s herr hal).2.2.2.1

/-- **The witness callee saves the caller's return address below `sp`**: after the call, the
16 bytes below the caller's `sp` hold the return address `pc + 4` and the caller's fp — a byte
that depends on the caller's pc, not on its world. This is the premise `hsave` under which the
former contract was proven unsatisfiable (`calleeOk_saves_lr_false`); `calleeOk_witness`
satisfies the new one. -/
theorem witness_saves_lr (g h : BitVec 64) (s : Arm.ArmState) (herr : Arm.r .ERR s = .None)
    (hal : Arm.CheckSPAlignment s) :
    Arm.read_mem_bytes 16 (spOf s - 16#64) (witnessCall g h s) = (Arm.r .PC s + 4#64) ++ xreg 29 s :=
  (framed_spec (keepsBut_framed keepsBut_id (by decide) h) (by decide) g s herr hal).2.2.2.2

/-- The witness TLSDESC hook: the static TLSDESC resolver's net effect — x0 the variable's
address (thread pointer plus offset: here the symbol), the temporary the thread pointer, the pc
after the sequence; no stack use. -/
def tlsWitness (sym : String → Int → BitVec 64) (tp : BitVec 64) (n : String) (tmp : Reg)
    (s : Arm.ArmState) : Arm.ArmState :=
  match tmp with
  | .x k => Arm.w .PC (Arm.r .PC s + 20) (Arm.w (.GPR (rnum k)) tp (Arm.w (.GPR 0#5) (sym n 0) s))
  | _ => Arm.w .PC (Arm.r .PC s + 20) s

/-- **The witness hooks**: every call runs `witnessCall g h`, the TLSDESC sequence
`tlsWitness`. -/
def witnessHooks (g h : BitVec 64) (sym : String → Int → BitVec 64) (tp : BitVec 64) : ArmHooks :=
  ⟨fun _ => witnessCall g h, tlsWitness sym tp⟩

/-- **The witness external semantics**: every callee returns nothing and leaves the world
unchanged; symbols at `sym`, thread pointer `tp`, the TLSDESC call keeps the flags. -/
def witnessX (sym : String → Int → BitVec 64) (tp : BitVec 64) : ExtSem :=
  ⟨fun _ _ w => some ([], w), sym, tp, fun _ w => Arm.read_pstate w⟩

theorem regVal_keep {s t : Arm.ArmState}
    (h : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f s) {r : Reg}
    (hr : ∀ n, r = .x n → n < 29) : regVal t r = regVal s r := by
  cases r with
  | x n =>
    have hn := hr n rfl
    simp only [regVal]
    rw [h _ (by simp) (fun e => rnum_ne (a := n) (b := 30) (by omega) (by omega) (by omega)
      (Arm.StateField.GPR.inj e))]
  | v n => simp only [regVal]; rw [h _ (by simp) (by simp)]
  | _ => rfl

/-- **A callee that keeps everything but the pc, x30 and its dead stack, and returns to
`pc + 4`, meets the callee contract** for every frame `F`, budget `K` and call sites `S`, with an
external semantics `X` that keeps the world and, at the call sites `S`, gives a value only to a
def in x0, the value x0 holds at the call (a callee returning its first argument, or nothing). -/
theorem calleeOk_of_keepsBut {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} (hk : ∀ d, KeepsBut K (H.call d))
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hw : ∀ d uses w outs w', X.call d uses w = some (outs, w') → w' = w)
    (hdef : ∀ info, S info → ∀ (c : CheckCtx) wh ops regs s w outs w',
      (MInst.call info).operands = .ok ops →
      c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok () →
      X.call (match info.dest with | .sym n => some n | .reg _ => none) (useVals ops regs s) w =
        some (outs, w') →
      ∀ p ∈ defRegs ops regs outs, p.1.2 = .x 0 ∧ p.2 = regVal s (.x 0)) :
    CalleeOk F K X H S := by
  refine ⟨fun ctx info hS s hKs hD c wh ops regs i' w outs w' hops hst hasg hww hal herr hsem => ?_,
    fun d s herr hal => hpc d s herr hal, fun d uses w outs w' hx herr => ?_⟩
  · simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    have hdefs := hdef info hS c wh ops regs s w o w2 hops hst hx
    obtain rfl := hw _ _ _ _ _ hx
    obtain ⟨ic, rfl⟩ := assign_call_form hasg
    obtain ⟨hf, hm, hp⟩ := hk (match ic.dest with | .sym n => some n | .reg _ => none) s herr hal
    have hnb : ∀ a, ¬ StackBelow K (spOf s) a →
        (H.call (match ic.dest with | .sym n => some n | .reg _ => none) s).mem a = s.mem a :=
      fun a ha => hm a fun hb => ha (stackBelow_of_belowMod hKs hb)
    have hex : callExec H (.call ic) s =
        some (H.call (match ic.dest with | .sym n => some n | .reg _ => none) s) := by
      simp only [callExec]; exact ite_eq_left_iff.mpr fun h => absurd hal h
    refine ⟨_, hex, ⟨fun f hf' => ?_, fun a ha => ?_, ?_⟩,
      ⟨hf _ (by simp) (by simp), fun a ha => hnb a ha.2⟩, fun p hp => ?_, fun r hr _ _ => ?_,
      fun r _ hcs => ?_⟩
    · have h1 : f ≠ .PC := fun e => hf' (by rw [e]; simp [Masked])
      have h2 : f ≠ .GPR 30#5 := fun e => hf' (by rw [e]; simp [Masked])
      rw [hf f h1 h2]; exact hww.1 f hf'
    · rw [hnb a fun hb => ha (hD a hb)]; exact hww.2.1 a ha
    · rw [hp]; exact hww.2.2
    · obtain ⟨h1, h2⟩ := hdefs p hp
      rw [h1, h2]
      exact regVal_keep hf fun n e => by cases e; omega
    · refine regVal_keep hf fun n e => ?_
      subst e
      rcases allocatable_cases hr with ⟨m, e, hm29, -⟩ | ⟨m, e, -⟩ <;> cases e
      exact hm29
    · refine congrArg _ (regVal_keep hf fun n e => ?_)
      subst e
      simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hcs
      rcases hcs with ⟨i, hi, e⟩ | ⟨i, hi, e⟩ <;> cases e
      omega
  · obtain rfl := hw _ _ _ _ _ hx
    exact ⟨herr, rfl⟩

/-- **The callee contract holds for the witness** — a callee that saves its return address
below `sp` (`witness_saves_lr`) — for every frame `F`, every budget `K ≥ 32` and every set of
call sites `S`. -/
theorem calleeOk_witness (F : BitVec 64 → Prop) {K : Nat} (hK : 32 ≤ K) (S : CallInfo → Prop)
    (g h : BitVec 64) (sym : String → Int → BitVec 64) (tp : BitVec 64) :
    CalleeOk F K (witnessX sym tp) (witnessHooks g h sym tp) S :=
  calleeOk_of_keepsBut (fun _ => keepsBut_mono (witnessCall_keepsBut g h) hK)
    (fun _ s herr hal => witnessCall_pc g h s herr hal)
    (fun _ _ _ _ _ hx => by simp only [witnessX, Option.some.injEq, Prod.mk.injEq] at hx; exact hx.2.symm)
    (fun _ _ _ _ _ _ _ _ outs _ _ _ hx p hp => by
      simp only [witnessX, Option.some.injEq, Prod.mk.injEq] at hx
      rw [← hx.1] at hp
      simp [defRegs] at hp)

theorem read_pstate_eq {s t : Arm.ArmState} (h : ∀ fl, Arm.r (.FLAG fl) s = Arm.r (.FLAG fl) t) :
    Arm.read_pstate s = Arm.read_pstate t := by
  have hN := h .N
  have hZ := h .Z
  have hC := h .C
  have hV := h .V
  simp only [Arm.r, Arm.read_base_flag] at hN hZ hC hV
  apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption

theorem read_pstate_w {f : Arm.StateField} (hf : ∀ fl, f ≠ .FLAG fl) (v) (s : Arm.ArmState) :
    Arm.read_pstate (Arm.w f v s) = Arm.read_pstate s :=
  read_pstate_eq fun fl => Arm.r_of_w_different (Ne.symm (hf fl))

/-- **The TLSDESC contract holds for the witness**, for every frame `F` and budget `K`, with an
external semantics whose TLSDESC call keeps the flags. -/
theorem tlsOk_witness (F : BitVec 64 → Prop) (K : Nat) (g h : BitVec 64) (X : ExtSem)
    (hfl : ∀ n w, X.tlsFlags n w = Arm.read_pstate w) :
    TlsOk F K X (witnessHooks g h X.sym X.tp) := by
  refine ⟨fun n tmp s _ => ?_, fun n k s hk29 hk0 _ _ _ _ _ => ?_, fun n k s w hw => ?_⟩
  · cases tmp <;> simp [witnessHooks, tlsWitness, Arm.r_of_w_same]
  · have h0k : (0#5 : BitVec 5) ≠ rnum k := fun e =>
      hk0 (by have := rnum_ne (a := 0) (b := k) (by omega) (by omega); simp_all [rnum])
    refine ⟨?_, ?_, fun f h1 h2 h3 _ _ => ?_, fun a _ => ?_, ?_⟩
    · simp only [witnessHooks, tlsWitness, xreg]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (fun e => h0k
        (Arm.StateField.GPR.inj e)), Arm.r_of_w_same]
    · simp only [witnessHooks, tlsWitness]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]
    · simp only [witnessHooks, tlsWitness]
      have h2' : f ≠ .GPR 0#5 := h2
      rw [Arm.r_of_w_different h1, Arm.r_of_w_different h3, Arm.r_of_w_different h2']
    · simp [witnessHooks, tlsWitness, Arm.ArmState.mem_w_eq_mem]
    · simp [witnessHooks, tlsWitness, Arm.w_program]
  · simp only [witnessHooks, tlsWitness, hfl]
    rw [read_pstate_w (fun _ => by simp), read_pstate_w (fun _ => by simp),
      read_pstate_w (fun _ => by simp)]
    exact read_pstate_eq fun fl => hw.1 _ (by simp [Masked])

/-- **The external contract holds for the witness** in an environment whose declared externs
`exts` return nothing (`sigRets`, no CLIF returns) and keep the memory, for every memory
relation `MR`. -/
theorem xCallsOk_witness {env : Clif.Env} {exts : List Clif.ExtFunc} (MR : MemRelT)
    (sym : String → Int → BitVec 64) (tp : BitVec 64)
    (hsig : ∀ ext ∈ exts, sigRets ext.sig = [] ∧ ext.sig.returns = [])
    (hnoop : ∀ ext ∈ exts, ∀ g, env.extern ext.name = some g → ∀ vals cm rvals cm',
      g vals cm = .returned rvals cm' → cm' = cm) :
    XCallsOk env exts MR (witnessX sym tp) := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg _ _ hmr hret hrl
  have h0 : rvals = [] := List.eq_nil_of_length_eq_zero (by rw [hrl, (hsig ext hin).2]; rfl)
  subst h0
  rw [hnoop ext hin g hg _ _ _ _ hret]
  exact ⟨[], w, rfl, by rw [(hsig ext hin).1]; rfl, ⟨Nat.le_refl _, fun _ _ _ h => nomatch h⟩, hmr⟩

/-- **The indirect-call contract holds for the witness** for call-site signatures without
returns, in an environment whose externs keep the memory (if there is a signature). -/
theorem xCallsIndOk_witness {env : Clif.Env} {sigs : List Clif.Signature} (MR : MemRelT)
    (sym : String → Int → BitVec 64) (tp : BitVec 64)
    (hsig : ∀ sig ∈ sigs, sigRets sig = [] ∧ sig.returns = [])
    (hnoop : ∀ sig ∈ sigs, ∀ n g, env.extern n = some g → ∀ vals cm rvals cm',
      g vals cm = .returned rvals cm' → cm' = cm) :
    XCallsIndOk env sigs MR (witnessX sym tp) := by
  intro sig hin n g sl cm w u args vals rvals cm' hg _ _ _ _ hmr hret hrl _
  have h0 : rvals = [] := List.eq_nil_of_length_eq_zero (by rw [hrl, (hsig sig hin).2]; rfl)
  subst h0
  rw [hnoop sig hin n g hg _ _ _ _ hret]
  exact ⟨[], w, rfl, by rw [(hsig sig hin).1]; rfl, ⟨Nat.le_refl _, fun _ _ _ h => nomatch h⟩, hmr⟩

/-! ## The premises of the end-to-end theorems -/

/-- The witness symbol addresses: the linked ones (`syms`) plus the addend. -/
def witnessSym (syms : String → Option Nat) (n : String) (off : Int) : BitVec 64 :=
  BitVec.ofNat 64 ((syms n).getD 0) + BitVec.ofInt 64 off

theorem witnessSym_ok (syms : String → Option Nat) :
    ∀ n b, syms n = some b → witnessSym syms n 0 = BitVec.ofNat 64 b := by
  intro n b h
  simp [witnessSym, h]

/-- **Non-vacuity of the contract premises of `backend_correct_final`** (and of `_opt_proven`,
`_legal`, `_linked`, which take the same ones for their compiled function): for a compiled
function whose externs and indirect-call signatures return nothing, in an environment whose
externs (those `f` declares; all of them if `f` has an indirect call) keep the memory when they
return, the witness hooks (every call runs a callee that pushes two frames
below `sp`, `witness_saves_lr`) and the witness external semantics meet the callee contract
`hC`, the TLSDESC contract `hTls`, the external contracts `hX`/`hXI` and the symbol premise
`hsym`, for every stack budget `K ≥ 32`. -/
theorem final_contracts_witness {f : Clif.Function} {vcp : VCode} {rf : RFunc} {af : AFunc}
    {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env} (hK : 32 ≤ K)
    (g h tp : BitVec 64)
    (hsig : ∀ ext ∈ f.externs.map (·.2), sigRets ext.sig = [] ∧ ext.sig.returns = [])
    (hisig : ∀ sig ∈ indSigs f, sigRets sig = [] ∧ sig.returns = [])
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ∀ G, env.extern ext.name = some G →
      ∀ vals cm rvals cm', G vals cm = .returned rvals cm' → cm' = cm)
    (hnoopI : ∀ sig ∈ indSigs f, ∀ n G, env.extern n = some G → ∀ vals cm rvals cm',
      G vals cm = .returned rvals cm' → cm' = cm) :
    (∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (witnessX (witnessSym syms) tp) (witnessHooks g h (witnessSym syms) tp) vcp.CallSite) ∧
    (∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (witnessX (witnessSym syms) tp) (witnessHooks g h (witnessSym syms) tp)) ∧
    (∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) (witnessX (witnessSym syms) tp)) ∧
    (∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) (witnessX (witnessSym syms) tp)) ∧
    (∀ n b, syms n = some b → (witnessX (witnessSym syms) tp).sym n 0 = BitVec.ofNat 64 b) :=
  ⟨fun _ => calleeOk_witness _ hK _ g h _ tp, fun _ => tlsOk_witness _ K g h (witnessX (witnessSym syms) tp) fun _ _ => rfl,
    fun _ => xCallsOk_witness _ _ tp hsig hnoop,
    fun _ => xCallsIndOk_witness _ _ tp hisig hnoopI, witnessSym_ok syms⟩

/-- **`backend_correct_final` with the witness callees**: for a function without `try_call`
whose externs and indirect-call signatures return nothing, in an environment whose externs keep
the memory, the Arm code run on the machine whose every call runs the witness callee (two frames
pushed below `sp`, the caller's return address saved there) refines the CLIF run, from the
run premises alone (with the callees' stack budget `K ≥ 32`). Every contract premise of
`backend_correct_final` is discharged (`final_contracts_witness`); `hCT` is vacuous without
`try_call`. -/
theorem backend_correct_final_witness {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env} (hK : 32 ≤ K)
    (g h tp : BitVec 64)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false)
    (hsig : ∀ ext ∈ f.externs.map (·.2), sigRets ext.sig = [] ∧ ext.sig.returns = [])
    (hisig : ∀ sig ∈ indSigs f, sigRets sig = [] ∧ sig.returns = [])
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ∀ G, env.extern ext.name = some G →
      ∀ vals cm rvals cm', G vals cm = .returned rvals cm' → cm' = cm)
    (hnoopI : ∀ sig ∈ indSigs f, ∀ n G, env.extern n = some G → ∀ vals cm rvals cm',
      G vals cm = .returned rvals cm' → cm' = cm)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX (witnessX (witnessSym syms) tp)
      (witnessHooks g h (witnessSym syms) tp) fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := f) (vcp := vcp) (rf := rf) (af := af) (slotOff := slotOff)
      hK g h tp hsig hisig hnoop hnoopI
  exact backend_correct_final hsub hc hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by rw [hnt B hB]; decide)) (fun _ => hTls) hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

/-! ## Callees that return a value -/

open Classical in
/-- **The witness external semantics with value-returning callees**: a callee whose name
satisfies `idf` returns its first argument (a `bl n`, or a `blr` whose target is the address
`sym n 0` of such a callee), every other one returns nothing; the world is unchanged. -/
noncomputable def idX (sym : String → Int → BitVec 64) (tp : BitVec 64) (idf : String → Prop) :
    ExtSem :=
  ⟨fun d uses w => some ((match d with
      | some n => if idf n then uses.take 1 else []
      | none => if ∃ n, idf n ∧ lo64 (uses.headD 0) = sym n 0 then (uses.drop 1).take 1 else []),
      w), sym, tp, fun _ w => Arm.read_pstate w⟩

/-- The call sites the value-returning witness serves (the shapes `gen_call_args` and
`gen_call_output` emit for callees of signature `(i64) -> i64` and for callees without results
with int arguments): a direct call of an `idf` callee with its argument and result in x0; a direct
call of any other callee; an indirect call (`blr` of an int vreg) with int arguments in registers
and no result, or with one argument and one result in x0. -/
def IdSite (idf : String → Prop) (info : CallInfo) : Prop :=
  (∃ n u d, idf n ∧ info = ⟨.sym n, retPairs [(u, .x 0)], callDefs [(.x 0, d)]⟩) ∨
  (∃ n, ¬ idf n ∧ info.dest = .sym n) ∨
  (∃ t L, info = ⟨.reg (.vreg t .int), retPairs L, callDefs []⟩) ∨
  (∃ t u d, info = ⟨.reg (.vreg t .int), retPairs [(u, .x 0)], callDefs [(.x 0, d)]⟩)

theorem defRegs_nil_right (ops : Array Operand) (regs : Array Reg) :
    defRegs ops regs [] = [] := by simp [defRegs]

/-- At the witness call sites, every def the witness semantics gives a value is x0, with the value
x0 held at the call. -/
theorem idSite_defs {idf : String → Prop} {sym : String → Int → BitVec 64} {tp : BitVec 64}
    {info : CallInfo} (hS : IdSite idf info) {c : CheckCtx} {wh : String} {ops : Array Operand}
    {regs : Array Reg} {s w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hops : (MInst.call info).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok ())
    (hx : (idX sym tp idf).call (match info.dest with | .sym n => some n | .reg _ => none)
      (useVals ops regs s) w = some (outs, w')) :
    w' = w ∧ ∀ p ∈ defRegs ops regs outs, p.1.2 = .x 0 ∧ p.2 = regVal s (.x 0) := by
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  simp only [Array.size_map] at hsz
  rcases hS with ⟨n, u, d, hn, rfl⟩ | ⟨n, hn, hd⟩ | ⟨t, L, rfl⟩ | ⟨t, u, d, rfl⟩
  · rw [operands_call_sym] at hops
    cases hops
    obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, regs = #[r0, r1] := by
      have h2 : regs.size = 2 := by simp [retOps, callDefOps] at hsz; omega
      exact ⟨regs[0], regs[1], Array.ext (by simp [h2]) fun i h1 h2' => by
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> rfl⟩
    have h0 := (hloc (⟨u, .int, .use, .early, .fixed (.x 0)⟩, .reg r0) (by simp [retOps, callDefOps])).2
      (.x 0) rfl
    have h1 := (hloc (⟨d, .int, .def, .late, .fixed (.x 0)⟩, .reg r1) (by simp [retOps, callDefOps])).2
      (.x 0) rfl
    simp only [Loc.reg.injEq] at h0 h1
    subst h0 h1
    simp only [idX, hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, fun p hp => ?_⟩
    simp [defRegs, useVals, retOps, callDefOps, Operand.isDef, Operand.isUse] at hp
    subst hp
    simp
  · rw [hd] at hx
    simp only [idX, hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, by simp [defRegs_nil_right]⟩
  · rw [operands_call_reg t L []] at hops
    cases hops
    simp only [idX, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    refine ⟨rfl, fun p hp => ?_⟩
    have hnd : ∀ q ∈ ((tgtOp t :: (retOps L ++ callDefOps [])).zip regs.toList),
        q.1.isDef = false := by
      intro q hq
      have hq1 := (List.of_mem_zip hq).1
      simp only [callDefOps, List.map_nil, List.append_nil, List.mem_cons, retOps,
        List.mem_map] at hq1
      rcases hq1 with e | ⟨a, -, e⟩
      · rw [e]; rfl
      · rw [← e]; rfl
    have : ((tgtOp t :: (retOps L ++ callDefOps [])).zip regs.toList).filter (·.1.isDef) = [] :=
      List.filter_eq_nil_iff.mpr fun q hq => by rw [hnd q hq]; decide
    simp only [defRegs, Array.toList_zip, this, List.zip_nil_left,
      List.not_mem_nil] at hp
  · rw [operands_call_reg t [(u, .x 0)] [(.x 0, d)]] at hops
    cases hops
    obtain ⟨r0, r1, r2, rfl⟩ : ∃ r0 r1 r2, regs = #[r0, r1, r2] := by
      have h3 : regs.size = 3 := by simp [retOps, callDefOps] at hsz; omega
      exact ⟨regs[0], regs[1], regs[2], Array.ext (by simp [h3]) fun i h1 h2' => by
        have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases this with rfl | rfl | rfl <;> rfl⟩
    have h1 := (hloc (⟨u, .int, .use, .early, .fixed (.x 0)⟩, .reg r1)
      (by simp [tgtOp, retOps, callDefOps])).2 (.x 0) rfl
    have h2 := (hloc (⟨d, .int, .def, .late, .fixed (.x 0)⟩, .reg r2)
      (by simp [tgtOp, retOps, callDefOps])).2 (.x 0) rfl
    simp only [Loc.reg.injEq] at h1 h2
    subst h1 h2
    simp only [idX, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨hout, rfl⟩ := hx
    refine ⟨rfl, fun p hp => ?_⟩
    split at hout
    · subst hout
      simp [defRegs, useVals, tgtOp, retOps, callDefOps, Operand.isDef, Operand.isUse] at hp
      subst hp
      simp
    · subst hout
      simp [defRegs_nil_right] at hp

theorem _root_.Backend.Proof.CalleeOk.mono {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S S' : CallInfo → Prop} (h : CalleeOk F K X H S) (hS : ∀ info, S' info → S info) :
    CalleeOk F K X H S' :=
  ⟨fun ctx info hi => h.os ctx info (hS info hi), h.pc, h.ext⟩

/-- **The callee contract holds for value-returning callees**: the witness callee (two frames
pushed below `sp`, x0 kept: it returns its first argument) with `idX` meets `CalleeOk` at the
witness call sites `IdSite idf`, for every frame `F` and budget `K ≥ 32`. Over every `CallInfo`
no callee returning a value could (a call whose def is x19 would force it to overwrite x19,
which a call without defs must preserve): the call sites are the compiled code's. -/
theorem calleeOk_id (F : BitVec 64 → Prop) {K : Nat} (hK : 32 ≤ K) (g h : BitVec 64)
    (sym : String → Int → BitVec 64) (tp : BitVec 64) (idf : String → Prop) :
    CalleeOk F K (idX sym tp idf) (witnessHooks g h sym tp) (IdSite idf) :=
  calleeOk_of_keepsBut (fun _ => keepsBut_mono (witnessCall_keepsBut g h) hK)
    (fun _ s herr hal => witnessCall_pc g h s herr hal)
    (fun _ _ _ _ _ hx => by simp only [idX, Option.some.injEq, Prod.mk.injEq] at hx; exact hx.2.symm)
    (fun _ hS _ _ _ _ _ _ _ _ hops hst hx => (idSite_defs hS hops hst hx).2)

/-- **The external contract holds for value-returning callees**: in an environment whose
declared `idf` externs take one register argument and return it (memory unchanged) and whose
other declared externs return nothing and keep the memory, with distinct symbol addresses of the
`idf` callees. -/
theorem xCallsOk_id {env : Clif.Env} {exts : List Clif.ExtFunc} (MR : MemRelT)
    (sym : String → Int → BitVec 64) (tp : BitVec 64) (idf : String → Prop)
    (hinj : ∀ a b, idf b → sym a 0 = sym b 0 → a = b)
    (hid : ∀ ext ∈ exts, idf ext.name →
      (∃ bytes, sigParamBytes ext.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ext.sig.params.length = 1 ∧ (sigRets ext.sig).length = 1 ∧
      ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → rvals = vals ∧ cm' = cm)
    (hnoop : ∀ ext ∈ exts, ¬ idf ext.name → sigRets ext.sig = [] ∧ ext.sig.returns = [] ∧
      ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → cm' = cm) :
    XCallsOk env exts MR (idX sym tp idf) := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hrl
  by_cases hi : idf ext.name
  · obtain ⟨⟨bytes, hb, h8⟩, hp1, hr1, hG⟩ := hid ext hin hi
    obtain ⟨rfl, rfl⟩ := hG g hg _ _ _ _ hret
    have hall : AllHold rvals args :=
      (argsAt_iff_of_regs hb h8 (hargs.1)).mp hargs
    have hl1 : args.length = 1 := by rw [← hall.1, hargs.1, hp1]
    have hx : (idX sym tp idf).call d uses w = some (args, w) := by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
      · simp only [idX, hi, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_true]
        exact List.take_of_length_le (by omega)
      · have hc : ∃ n, idf n ∧ lo64 ((ofX (sym ext.name 0) :: args).headD 0) = sym n 0 :=
          ⟨ext.name, hi, by simp [lo64_ofX]⟩
        simp only [idX, hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_true, List.drop_one,
          List.tail_cons]
        exact List.take_of_length_le (by omega)
    exact ⟨args, w, hx, by rw [hl1, hr1], hall.prefixHold, hmr⟩
  · obtain ⟨hs0, hr0, hG⟩ := hnoop ext hin hi
    have h0 : rvals = [] := List.eq_nil_of_length_eq_zero (by rw [hrl, hr0]; rfl)
    subst h0
    rw [hG g hg _ _ _ _ hret]
    have hx : (idX sym tp idf).call d uses w = some ([], w) := by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
      · simp [idX, hi]
      · have hc : ¬ ∃ n, idf n ∧ lo64 ((ofX (sym ext.name 0) :: args).headD 0) = sym n 0 := by
          rintro ⟨n, hn, e⟩
          simp only [List.headD_cons, lo64_ofX] at e
          exact hi (hinj _ _ hn e ▸ hn)
        simp only [idX, hc, ↓reduceIte]
    exact ⟨[], w, hx, by rw [hs0]; rfl, ⟨Nat.le_refl _, fun _ _ _ h => nomatch h⟩, hmr⟩

/-- **Non-vacuity with value-returning callees**: for a compiled function without indirect calls
whose call sites have the witness shapes (`IdSite idf`: direct calls of `(i64) -> i64` callees
`idf`, calls of callees without results), in an environment whose `idf` externs return their
argument and whose other externs return nothing (memory unchanged), with distinct addresses
of the `idf` callees, the witness hooks and `idX` meet `hC`, `hTls`, `hX` and `hXI`, for every
stack budget `K ≥ 32`. -/
theorem final_contracts_id {f : Clif.Function} {vcp : VCode} {rf : RFunc} {af : AFunc}
    {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env} (hK : 32 ≤ K)
    (g h tp : BitVec 64) (sym : String → Int → BitVec 64) (idf : String → Prop)
    (hsites : ∀ info, vcp.CallSite info → IdSite idf info)
    (hinj : ∀ a b, idf b → sym a 0 = sym b 0 → a = b)
    (hid : ∀ ext ∈ f.externs.map (·.2), idf ext.name →
      (∃ bytes, sigParamBytes ext.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ext.sig.params.length = 1 ∧ (sigRets ext.sig).length = 1 ∧
      ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → rvals = vals ∧ cm' = cm)
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ¬ idf ext.name → sigRets ext.sig = [] ∧
      ext.sig.returns = [] ∧ ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → cm' = cm)
    (hind : indSigs f = []) :
    (∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (idX sym tp idf) (witnessHooks g h sym tp) vcp.CallSite) ∧
    (∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (idX sym tp idf) (witnessHooks g h sym tp)) ∧
    (∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) (idX sym tp idf)) ∧
    (∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) (idX sym tp idf)) :=
  ⟨fun _ => (calleeOk_id _ hK g h sym tp idf).mono hsites,
    fun _ => tlsOk_witness _ K g h (idX sym tp idf) fun _ _ => rfl,
    fun _ => xCallsOk_id _ sym tp idf hinj hid hnoop,
    fun _ => by rw [hind]; exact xCallsIndOk_nil _ _ _⟩

/-- **`backend_correct_final` with value-returning witness callees**: for a function without
`try_call` and without indirect calls whose call sites have the witness shapes, calling `(i64) ->
i64` externs that return their argument and externs without results that keep the memory, the
Arm code run on the machine whose every call runs the witness callee (two frames pushed below
`sp`, x0 kept) refines the CLIF run from the run premises, the form coverage and the linked
symbol addresses alone. -/
theorem backend_correct_final_id {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env} (hK : 32 ≤ K)
    (g h tp : BitVec 64) (sym : String → Int → BitVec 64) (idf : String → Prop)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hnt : ∀ B ∈ f.blocks, B.term.isTry = false) (hind : indSigs f = [])
    (hsites : ∀ info, vcp.CallSite info → IdSite idf info)
    (hinj : ∀ a b, idf b → sym a 0 = sym b 0 → a = b)
    (hid : ∀ ext ∈ f.externs.map (·.2), idf ext.name →
      (∃ bytes, sigParamBytes ext.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ext.sig.params.length = 1 ∧ (sigRets ext.sig).length = 1 ∧
      ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → rvals = vals ∧ cm' = cm)
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ¬ idf ext.name → sigRets ext.sig = [] ∧
      ext.sig.returns = [] ∧ ∀ G, env.extern ext.name = some G → ∀ vals cm rvals cm',
        G vals cm = .returned rvals cm' → cm' = cm)
    (hsym : ∀ n b, syms n = some b → sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX (idX sym tp idf) (witnessHooks g h sym tp) fa) s
      (Clif.runLoop env p fuel cs) := by
  obtain ⟨hC, hTls, hX, hXI⟩ :=
    final_contracts_id (f := f) (vcp := vcp) (rf := rf) (af := af) (syms := syms)
      (slotOff := slotOff) hK g h tp sym idf hsites hinj hid hnoop hind
  exact backend_correct_final hsub hc hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by rw [hnt B hB]; decide)) (fun _ => hTls) hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

/-! ## Functions with `try_call` -/

/-- **The `try_call` callee contract holds for the witness**: at `try_call` sites whose callee
returns nothing (`ti.rets = 0`: the call's defs are the exception payload registers x0/x1 only),
`CalleeTryOk` holds for every hook, in particular for the witness callee, which leaves x0/x1 as
the caller had them (the former contract fixed them to `X.call`'s world, which masks the
caller's registers: unsatisfiable for such a callee). -/
theorem calleeTryOk_witness {vcp : VCode} (hrets : ∀ info ti, vcp.TrySite info ti → ti.rets = 0)
    (F : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) : CalleeTryOk F X H vcp.TrySite :=
  calleeTryOk_of_rets0 hrets

/-- **`backend_correct_final` with the witness callees, for a function with `try_call`s**: for
a function whose externs and indirect-call signatures return nothing (so its `try_call` sites
define only the exception payload registers, `hrets`), in an environment whose externs keep the
memory, the Arm code run on the machine whose every call runs the witness callee (two frames
pushed below `sp`, x0/x1 left as they were) refines the CLIF run on the runs where every callee
of a `try_call` returns normally, from the run premises alone. Every contract premise of
`backend_correct_final`, `hCT` included, is discharged. -/
theorem backend_correct_final_try_witness {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {syms : String → Option Nat} {slotOff K : Nat} {env : Clif.Env} (hK : 32 ≤ K)
    (g h tp : BitVec 64)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hrets : ∀ info ti, vcp.TrySite info ti → ti.rets = 0)
    (hsig : ∀ ext ∈ f.externs.map (·.2), sigRets ext.sig = [] ∧ ext.sig.returns = [])
    (hisig : ∀ sig ∈ indSigs f, sigRets sig = [] ∧ sig.returns = [])
    (hnoop : ∀ ext ∈ f.externs.map (·.2), ∀ G, env.extern ext.name = some G →
      ∀ vals cm rvals cm', G vals cm = .returned rvals cm' → cm' = cm)
    (hnoopI : ∀ sig ∈ indSigs f, ∀ n G, env.extern n = some G → ∀ vals cm rvals cm',
      G vals cm = .returned rvals cm' → cm' = cm)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX (witnessX (witnessSym syms) tp)
      (witnessHooks g h (witnessSym syms) tp) fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := f) (vcp := vcp) (rf := rf) (af := af) (slotOff := slotOff)
      hK g h tp hsig hisig hnoop hnoopI
  exact backend_correct_final hsub hc hcov hC (fun _ _ => calleeTryOk_witness hrets _ _ _)
    (fun _ => hTls) hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

end E2E
