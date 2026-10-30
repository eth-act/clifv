import FV.E2E.ExecTlsWords
import FV.E2E.ExecTls

/-! # The simulation by the hook-free executable machine (T1)

`act_simT`: the model's activations (the machine of `binary_correct_exec_proven` with the base
environment `leBase I B file`) are simulated by `stepT`, the processor on the executable's words
including lld's local-exec TLS words; `exec_of_modelT` transfers the model's outcome. The proof is
`act_coreN`'s, with one more case: at a TLS sequence the model's two steps (`adrp`, the hook
`leTls`) are the executable's six (`tls_step`).
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck E2E.ExecWords

theorem _root_.Backend.Insn.tlsSite_of_hooked {x : Insn} (h : x.hooked = false) :
    x.tlsSite = false := by
  cases x <;> simp_all [Insn.hooked, Insn.tlsSite]

theorem _root_.Backend.Insn.tlsSite_of_reloc {i : Insn} {ty : RelocType} {s : String} {a : Int}
    (h : i.reloc? = some (ty, s, a)) (ht : ty = .adrGotPage ∨ ty = .adrPrelPgHi21) :
    i.tlsSite = false := by
  rcases ht with rfl | rfl <;> cases i <;> simp_all [Insn.reloc?, Insn.tlsSite]

section Tls

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- `stepT` at a TLS site or a real site: the processor on the file's word. -/
theorem stepT_real {s : Arm.ArmState} {x : Site} (hs : siteAt I (Arm.r .PC s) = some x)
    (hx : x = .tlsAdrp ∨ (∃ tmp n, x = .tls tmp n) ∨ x = .real) {a : Arm.ArmInst}
    (herr : Arm.r .ERR s = .None)
    (hw : (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst = some a) :
    stepT I B file s = Arm.exec_inst a s := by
  unfold stepT
  rw [hs]
  rcases hx with rfl | ⟨tmp, n, rfl⟩ | rfl
  · exact realStep_eq herr hw
  · exact realStep_eq herr hw
  · exact realStep_eq herr hw

theorem fileWord_bind {a : BitVec 64} {w : BitVec 32} {i : Arm.ArmInst}
    (hf : fileWord file a = some w) (hd : Arm.decode_raw_inst w = some i) :
    (fileWord file a).bind Arm.decode_raw_inst = some i := by
  rw [hf, Option.bind_some, hd]

theorem wAt_add20 (a : Art) (o : Nat) : wAt a (o + 20) + 4 = wAt a o + 4 + 20 := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add]
  rfl

theorem encZR_ne0 {tmp : Reg} {rt : BitVec 5} (htmp : tmp ≠ .x 0) (hrt : tmp.encZR = .ok rt) :
    rt ≠ 0#5 := by
  rintro rfl
  cases tmp with
  | x k =>
    simp only [Reg.encZR] at hrt
    split at hrt
    · have := congrArg BitVec.toNat (Except.ok.inj hrt)
      simp at this
      exact htmp (by rw [show k = 0 by omega])
    · cases hrt
  | _ => simp [Reg.encZR] at hrt <;> cases hrt

/-- The compiled `mrs tmp, tpidr_el0`. -/
theorem mrs_arm {env : Env} {tmp : Reg} {rt : BitVec 5} {a : Arm.ArmInst}
    (hrt : tmp.encZR = .ok rt) (h : (Insn.mrsTpidrEl0 tmp).toArmInst env = .ok a) :
    a = .BR (.Mrs
      {o0 := 1, op1 := 0b011#3, CRn := 0b1101#4, CRm := 0, op2 := 0b010#3, Rt := rt}) := by
  simp [Insn.toArmInst, Insn.armFields, hrt, Functor.map, Except.map, bind, Except.bind, pure,
    Except.pure, Arm.ArmInst.norm] at h
  exact h.symm

/-- The compiled `add x0, x0, tmp`. -/
theorem add_arm {env : Env} {tmp : Reg} {rt : BitVec 5} {a : Arm.ArmInst}
    (hrt : tmp.encZR = .ok rt)
    (h : (Insn.aluRRR .add true (.x 0) (.x 0) tmp).toArmInst env = .ok a) :
    a = .DPR (.Add_sub_shifted_reg
      {sf := 1#1, op := 0#1, S := 0#1, shift := 0, Rm := rt, imm6 := 0, Rn := 0#5, Rd := 0#5}) := by
  have h0 : (Reg.x 0).encZR = .ok 0#5 := rfl
  simp [Insn.toArmInst, Insn.armFields, hrt, h0, ALUOp.addSub?, ALUOp.logic?, b1,
    Functor.map, Except.map, bind, Except.bind, pure, Except.pure, Arm.ArmInst.norm] at h
  exact h.symm

theorem add_exec (rt : BitVec 5) (s : Arm.ArmState) :
    Arm.exec_inst (.DPR (.Add_sub_shifted_reg
      {sf := 1#1, op := 0#1, S := 0#1, shift := 0, Rm := rt, imm6 := 0, Rn := 0#5, Rd := 0#5})) s =
    Arm.w .PC (Arm.r .PC s + 4)
      (Arm.w (.GPR 0#5) (Arm.r (.GPR 0#5) s + Arm.read_gpr_zr 64 rt s) s) := by
  rw [Arm.w_of_w_commute (by simp)]
  simp [Arm.exec_inst, Arm.DPR.exec_add_sub_shifted_reg, Arm.write_gpr_zr, Arm.write_gpr,
    Arm.read_gpr_zr, Arm.read_gpr, Arm.write_pc, Arm.read_pc, Arm.fst_AddWithCarry_eq_add,
    Arm.decode_shift, Arm.shift_reg]

theorem wzr_ne {rt : BitVec 5} (h : rt ≠ 31#5) (x : BitVec 64) (s : Arm.ArmState) :
    Arm.write_gpr_zr 64 rt x s = Arm.w (.GPR rt) x s := by
  simp [Arm.write_gpr_zr, h, Arm.write_gpr]

theorem rzr_ne {rt : BitVec 5} (h : rt ≠ 31#5) (s : Arm.ArmState) :
    Arm.read_gpr_zr 64 rt s = Arm.r (.GPR rt) s := by
  simp [Arm.read_gpr_zr, h, Arm.read_gpr]

/-- The end of the TLS sequence: the model's `leTls` state (unfolded) against the executable's
state after the six words. -/
theorem tls_sim_end {m e e5 : Arm.ArmState} (hs : Sim I m e) {rt : BitVec 5} (hrt0 : rt ≠ 0#5)
    {tp T off addr y q1 q2 q3 q4 q5 q6 : BitVec 64} (hT : T = tp) (haddr : tp + off = addr)
    (he5 : e5 = Arm.w .PC q5 (Arm.write_gpr_zr 64 rt T (Arm.w .PC q4 (Arm.w .PC q3 (Arm.w .PC q2
      (Arm.w (.GPR 0#5) off (Arm.w .PC q1 (Arm.w (.GPR 0#5) y e))))))))
    (hq6 : q6 = Arm.r .PC m + 4 + 20) :
    Sim I (if rt = 31#5 then
        Arm.w .PC (Arm.r .PC (Arm.w .PC (Arm.r .PC m + 4) m) + 20)
          (Arm.w (.GPR 0#5) off (Arm.w .PC (Arm.r .PC m + 4) m))
      else
        Arm.w .PC (Arm.r .PC (Arm.w .PC (Arm.r .PC m + 4) m) + 20)
          (Arm.w (.GPR rt) tp (Arm.w (.GPR 0#5) addr (Arm.w .PC (Arm.r .PC m + 4) m))))
      (Arm.w .PC q6 (Arm.w (.GPR 0#5) (Arm.r (.GPR 0#5) e5 + Arm.read_gpr_zr 64 rt e5) e5)) := by
  subst hT hq6
  rw [Arm.r_of_w_same]
  by_cases h31 : rt = 31#5
  · have hg : Arm.r (.GPR 0#5) e5 + Arm.read_gpr_zr 64 rt e5 = off := by
      subst he5 h31
      simp [Arm.read_gpr_zr, Arm.write_gpr_zr, Arm.r_of_w_different, Arm.r_of_w_same]
    rw [hg]
    simp only [h31, ↓reduceIte]
    have he5' : e5 = Arm.w .PC q5 (Arm.w .PC q4 (Arm.w .PC q3 (Arm.w .PC q2
        (Arm.w (.GPR 0#5) off (Arm.w .PC q1 (Arm.w (.GPR 0#5) y e)))))) := by
      subst h31; rw [he5]; simp [Arm.write_gpr_zr]
    refine ⟨fun fld => ?_, fun a ha => ?_⟩
    · by_cases hP : fld = .PC
      · subst hP; simp only [Arm.r_of_w_same]
      by_cases h0 : fld = .GPR 0#5
      · subst h0; simp [Arm.r_of_w_different, Arm.r_of_w_same]
      simp only [Arm.r_of_w_different hP, Arm.r_of_w_different h0, he5']
      exact hs.1 fld
    · simp only [Arm.ArmState.mem_w_eq_mem, he5']
      exact hs.2 a ha
  · simp only [h31, ↓reduceIte]
    have hg : Arm.r (.GPR 0#5) e5 + Arm.read_gpr_zr 64 rt e5 = addr := by
      subst he5
      simp [rzr_ne h31, wzr_ne h31, Arm.r_of_w_different, Arm.r_of_w_same, Ne.symm hrt0]
      rw [← haddr, BitVec.add_comm]
    rw [hg, wzr_ne h31] at *
    refine ⟨fun fld => ?_, fun a ha => ?_⟩
    · by_cases hP : fld = .PC
      · subst hP; simp only [Arm.r_of_w_same]
      by_cases h0 : fld = .GPR 0#5
      · subst h0; simp [Arm.r_of_w_different, Arm.r_of_w_same, Ne.symm hrt0]
      by_cases hr : fld = .GPR rt
      · subst hr he5; simp [Arm.r_of_w_different, Arm.r_of_w_same, hrt0]
      simp only [Arm.r_of_w_different hP, Arm.r_of_w_different h0, Arm.r_of_w_different hr, he5]
      exact hs.1 fld
    · simp only [Arm.ArmState.mem_w_eq_mem, he5]
      exact hs.2 a ha

/-- **The TLS sequence**: from the model state at its `adrp`, the model's two steps (the `adrp`,
then the hook `leTls` at the `ldr`) against the executable's six processor steps on lld's
local-exec words (`movz`, `movk`, `nop`, `nop`, `mrs`, `add`), given the loader's thread pointer
and the variable's address (`TlsLoader`). -/
theorem tls_step {M : Nat} {g : Clif.Function} (hF : FnOk I file g)
    (hT : TlsClosed (art I g).fa.lines.toList)
    (hsite : ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i))
    {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .tlsDescAdrPage21)
    {m e : Arm.ArmState} (hpc : Arm.r .PC m = wAt (art I g) rl.offset)
    (herr : Arm.r .ERR m = .None) (hprog : m.program = (art I g).fb.program (art I g).base)
    (hs : Sim I m e) (htp : Arm.r .TPIDR m = B.tp)
    (haddr : B.tp + tpOffOf I file rl.sym = I.symAddr rl.sym 0) :
    Sim I ((sys I (leBase I B file)).mach M g ((sys I (leBase I B file)).mach M g m))
      (runX (stepT I B file) 6 e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, ho, tmp, htmp, ⟨t1, hj1⟩, ⟨t2, hj2⟩, ⟨t3, hj3⟩, ⟨t4, hj4⟩, ⟨t5, hj5⟩⟩ :=
    tls_lines hF hT hrl ht
  -- the offsets of the six lines
  have o1 : lineOffset (art I g).fa.lines.toList (j + 1) = rl.offset + 4 := by
    rw [lineOffset_succ _ _ _ hj, ho]; rfl
  have o2 : lineOffset (art I g).fa.lines.toList (j + 2) = rl.offset + 8 := by
    rw [lineOffset_succ _ _ _ hj1, o1]; rfl
  have o3 : lineOffset (art I g).fa.lines.toList (j + 3) = rl.offset + 12 := by
    rw [lineOffset_succ _ _ _ hj2, o2]; rfl
  have o4 : lineOffset (art I g).fa.lines.toList (j + 4) = rl.offset + 16 := by
    rw [lineOffset_succ _ _ _ hj3, o3]; rfl
  have o5 : lineOffset (art I g).fa.lines.toList (j + 5) = rl.offset + 20 := by
    rw [lineOffset_succ _ _ _ hj4, o4]; rfl
  -- the sites of the six words
  have s0 := hsite _ _ (insnAt_of_line hF hj)
  have s1 := hsite _ _ (insnAt_of_line hF hj1)
  have s2 := hsite _ _ (insnAt_of_line hF hj2)
  have s3 := hsite _ _ (insnAt_of_line hF hj3)
  have s4 := hsite _ _ (insnAt_of_line hF hj4)
  have s5 := hsite _ _ (insnAt_of_line hF hj5)
  rw [ho] at s0
  rw [o1] at s1
  rw [o2] at s2
  rw [o3] at s3
  rw [o4] at s4
  rw [o5] at s5
  -- the words: lld's local-exec relaxation, then the compiled `mrs` and `add`
  have hR := hF.bin.reloc rl hrl
  unfold RelocOk at hR
  rw [ht] at hR
  obtain ⟨-, v, hv, hv32, hw0, hw1, hw2, hw3⟩ := hR
  have hhi : v / 65536 < 2 ^ 16 := by omega
  have hlo : v % 65536 < 2 ^ 16 := by omega
  obtain ⟨hd0, hx0⟩ := movzW_exec hhi
  obtain ⟨hd1, hx1⟩ := movkW_exec hlo
  obtain ⟨hdn, hxn⟩ := nopW_exec
  obtain ⟨w4, he4, hf4⟩ := fileWord_plain hF hm hj4 rfl
  obtain ⟨a4, ha4, hd4⟩ := Insn.decode_encode he4
  obtain ⟨w5, he5, hf5⟩ := fileWord_plain hF hm hj5 rfl
  obtain ⟨a5, ha5, hd5⟩ := Insn.decode_encode he5
  rw [o4] at hf4
  rw [o5] at hf5
  -- the temporary's register
  obtain ⟨rt, hrt⟩ : ∃ rt, tmp.encZR = .ok rt := by
    cases h : tmp.encZR with
    | error _ =>
      simp [Insn.toArmInst, Insn.armFields, h, Functor.map, Except.map, bind, Except.bind] at ha4
    | ok rt => exact ⟨rt, rfl⟩
  have hrt0 := encZR_ne0 htmp hrt
  have ha4' := mrs_arm hrt ha4
  subst ha4'
  have hx4 := Arm.exec_mrs_tpidr rt
  have ha5' := add_arm hrt ha5
  subst ha5'
  have hx5 := add_exec rt
  -- the executable's run
  have hpe : Arm.r .PC e = wAt (art I g) rl.offset := (hs.1 .PC).trans hpc
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans herr
  have hte : Arm.r .TPIDR e = B.tp := (hs.1 .TPIDR).trans htp
  obtain ⟨e1, he1d⟩ : ∃ e1, e1 = Arm.w .PC (Arm.r .PC e + 4)
      (Arm.w (.GPR 0#5) (BitVec.ofNat 64 (v / 65536 * 2 ^ 16)) e) := ⟨_, rfl⟩
  have he1 : stepT I B file e = e1 := by
    rw [stepT_real (by rw [hpe]; exact s0) (.inl rfl) hee
      (fileWord_bind (by rw [hpe]; exact hw0) hd0), hx0, he1d]
  have pc1 : Arm.r .PC e1 = wAt (art I g) (rl.offset + 4) := by
    rw [he1d, Arm.r_of_w_same, hpe, wAt_add4]
  have err1 : Arm.r .ERR e1 = .None := by rw [he1d]; simp [Arm.r_of_w_different, hee]
  obtain ⟨e2, he2d⟩ : ∃ e2, e2 = Arm.w .PC (Arm.r .PC e1 + 4)
      (Arm.w (.GPR 0#5) (BitVec.ofNat 64 v) e1) := ⟨_, rfl⟩
  have he2 : stepT I B file e1 = e2 := by
    rw [stepT_real (by rw [pc1]; exact s1) (.inr (.inl ⟨_, _, rfl⟩)) err1
      (fileWord_bind (by rw [pc1]; exact hw1) hd1), hx1, he2d]
    congr 2
    rw [he1d, Arm.r_of_w_different (by simp), Arm.r_of_w_same]
    exact movz_movk_val hv32
  have pc2 : Arm.r .PC e2 = wAt (art I g) (rl.offset + 8) := by
    rw [he2d, Arm.r_of_w_same, pc1, wAt_add4]
  have err2 : Arm.r .ERR e2 = .None := by rw [he2d]; simp [Arm.r_of_w_different, err1]
  obtain ⟨e3, he3d⟩ : ∃ e3, e3 = Arm.w .PC (Arm.r .PC e2 + 4) e2 := ⟨_, rfl⟩
  have he3 : stepT I B file e2 = e3 := by
    rw [stepT_real (by rw [pc2]; exact s2) (.inr (.inr rfl)) err2
      (fileWord_bind (by rw [pc2]; exact hw2) hdn), hxn, he3d]
  have pc3 : Arm.r .PC e3 = wAt (art I g) (rl.offset + 12) := by
    rw [he3d, Arm.r_of_w_same, pc2, wAt_add4]
  have err3 : Arm.r .ERR e3 = .None := by rw [he3d]; simp [Arm.r_of_w_different, err2]
  obtain ⟨e4, he4d⟩ : ∃ e4, e4 = Arm.w .PC (Arm.r .PC e3 + 4) e3 := ⟨_, rfl⟩
  have he4 : stepT I B file e3 = e4 := by
    rw [stepT_real (by rw [pc3]; exact s3) (.inr (.inr rfl)) err3
      (fileWord_bind (by rw [pc3]; exact hw3) hdn), hxn, he4d]
  have pc4 : Arm.r .PC e4 = wAt (art I g) (rl.offset + 16) := by
    rw [he4d, Arm.r_of_w_same, pc3, wAt_add4]
  have err4 : Arm.r .ERR e4 = .None := by rw [he4d]; simp [Arm.r_of_w_different, err3]
  obtain ⟨e5, he5d⟩ : ∃ e5, e5 = Arm.w .PC (Arm.r .PC e4 + 4)
      (Arm.write_gpr_zr 64 rt (Arm.r .TPIDR e4) e4) := ⟨_, rfl⟩
  have he5 : stepT I B file e4 = e5 := by
    rw [stepT_real (by rw [pc4]; exact s4) (.inr (.inr rfl)) err4
      (fileWord_bind (by rw [pc4]; exact hf4) hd4), hx4, he5d]
  have pc5 : Arm.r .PC e5 = wAt (art I g) (rl.offset + 20) := by
    rw [he5d, Arm.r_of_w_same, pc4, wAt_add4]
  have err5 : Arm.r .ERR e5 = .None := by
    rw [he5d]; simp [Arm.r_of_w_different, Arm.write_gpr_zr, Arm.write_gpr]; split <;>
      simp [Arm.r_of_w_different, err4]
  have he6 : stepT I B file e5 = Arm.w .PC (Arm.r .PC e5 + 4)
      (Arm.w (.GPR 0#5) (Arm.r (.GPR 0#5) e5 + Arm.read_gpr_zr 64 rt e5) e5) := by
    rw [stepT_real (by rw [pc5]; exact s5) (.inr (.inr rfl)) err5
      (fileWord_bind (by rw [pc5]; exact hf5) hd5), hx5]
  have hrun : runX (stepT I B file) 6 e = Arm.w .PC (Arm.r .PC e5 + 4)
      (Arm.w (.GPR 0#5) (Arm.r (.GPR 0#5) e5 + Arm.read_gpr_zr 64 rt e5) e5) := by
    simp only [runX, he1, he2, he3, he4, he5, he6]
  -- the model's two steps
  have hb : progBase m = (art I g).base := progBase_of hF hm hprog hj
  have hi0 : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some (.adrpTlsDesc (.x 0) rl.sym) := by
    rw [hb, hpc, ← ho]; exact insnAt_of_line hF hj
  have hm1 : (sys I (leBase I B file)).mach M g m = Arm.w .PC (Arm.r .PC m + 4) m := by
    show ArmStepX (sys I (leBase I B file)).Xb ((sys I (leBase I B file)).hooks M) (art I g).fa m = _
    simp only [ArmStepX, hi0]
  have hb1 : progBase (Arm.w .PC (Arm.r .PC m + 4) m) = (art I g).base := by
    rw [← hb]; simp [progBase, Arm.w_program]
  have hi1 : insnAt (art I g).fa (progBase (Arm.w .PC (Arm.r .PC m + 4) m))
      (Arm.r .PC (Arm.w .PC (Arm.r .PC m + 4) m)) = some (.ldrTlsDescLo12 tmp (.x 0) rl.sym) := by
    rw [hb1, Arm.r_of_w_same, hpc, wAt_add4, ← o1]; exact insnAt_of_line hF hj1
  have hm2 : (sys I (leBase I B file)).mach M g (Arm.w .PC (Arm.r .PC m + 4) m) =
      leTls I B file rl.sym tmp (Arm.w .PC (Arm.r .PC m + 4) m) := by
    show ArmStepX (sys I (leBase I B file)).Xb ((sys I (leBase I B file)).hooks M) (art I g).fa _ = _
    simp only [ArmStepX, hi1, hooks_tls]
    rfl
  rw [hm1, hm2, hrun]
  -- the final states
  have hx4e : Arm.r .TPIDR e4 = B.tp := by
    rw [he4d, he3d, he2d, he1d]; simp [Arm.r_of_w_different, hte]
  have hoff : tpOffOf I file rl.sym = BitVec.ofNat 64 v := by simp [tpOffOf, hv]
  have hgd : tmp.encZR.toOption.getD 31#5 = rt := by simp [hrt, Except.toOption]
  have haddr' : B.tp + BitVec.ofNat 64 v = I.symAddr rl.sym 0 := by rw [← hoff]; exact haddr
  have hq6 : Arm.r .PC e5 + 4 = Arm.r .PC m + 4 + 20 := by rw [pc5, hpc, wAt_add20]
  unfold leTls
  rw [hgd, hoff]
  subst he5d he4d he3d he2d he1d
  exact tls_sim_end hs hrt0 hx4e haddr' rfl hq6

/-- At a TLS sequence's `adrp`, the executable's first step has the model's pc and error (for a
trap at the `ldr` word). -/
theorem tls_first_pc {M : Nat} {g : Clif.Function} (hF : FnOk I file g)
    (hT : TlsClosed (art I g).fa.lines.toList)
    (hsite : ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i))
    {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .tlsDescAdrPage21)
    {m e : Arm.ArmState} (hpc : Arm.r .PC m = wAt (art I g) rl.offset)
    (herr : Arm.r .ERR m = .None) (hprog : m.program = (art I g).fb.program (art I g).base)
    (hs : Sim I m e) :
    Arm.r .PC ((sys I (leBase I B file)).mach M g m) = Arm.r .PC (stepT I B file e) ∧
      Arm.r .ERR ((sys I (leBase I B file)).mach M g m) = Arm.r .ERR (stepT I B file e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, ho, -⟩ := tls_lines hF hT hrl ht
  have s0 := hsite _ _ (insnAt_of_line hF hj)
  rw [ho] at s0
  have hR := hF.bin.reloc rl hrl
  unfold RelocOk at hR
  rw [ht] at hR
  obtain ⟨-, v, -, hv32, hw0, -⟩ := hR
  have hhi : v / 65536 < 2 ^ 16 := by omega
  obtain ⟨hd0, hx0⟩ := movzW_exec hhi
  have hpe : Arm.r .PC e = wAt (art I g) rl.offset := (hs.1 .PC).trans hpc
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans herr
  have hb : progBase m = (art I g).base := progBase_of hF hm hprog hj
  have hi0 : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some (.adrpTlsDesc (.x 0) rl.sym) := by
    rw [hb, hpc, ← ho]; exact insnAt_of_line hF hj
  have hm1 : (sys I (leBase I B file)).mach M g m = Arm.w .PC (Arm.r .PC m + 4) m := by
    show ArmStepX (sys I (leBase I B file)).Xb ((sys I (leBase I B file)).hooks M) (art I g).fa m = _
    simp only [ArmStepX, hi0]
  rw [hm1, stepT_real (by rw [hpe]; exact s0) (.inl rfl) hee
    (fileWord_bind (by rw [hpe]; exact hw0) hd0), hx0]
  refine ⟨by rw [Arm.r_of_w_same, Arm.r_of_w_same, hpc, hpe], ?_⟩
  simp [Arm.r_of_w_different, herr, hee]

end Tls

/-! ## The simulation -/

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- `ret_not_secondN` for TLSDESC `ldr` words: the return address of a call of `h` is no TLSDESC
`ldr` word of `h` reached in `h`'s activation (its `adrp` would be the call's word). -/
theorem ret_not_tlsSecondN (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : ∀ g ∈ (prog I).funcs, TlsClosed (art I g).fa.lines.toList) {M M' : Nat}
    {g h : Clif.Function} (hg : g ∈ (prog I).funcs) (hh : h ∈ (prog I).funcs) {m : Arm.ArmState}
    (hok0 : StepOk I B file M g m) (hc : CallsAt I B g m h)
    (hrun' : RunTlsN I B M' h (enterAt (art I h) m)) {N : Nat}
    (hN : RetOf (art I h) m (runX ((sys I B).mach M' h) N (enterAt (art I h) m)))
    (hmin : ∀ j < N, ¬ RetOf (art I h) m (runX ((sys I B).mach M' h) j (enterAt (art I h) m)))
    (hsite : ∀ g ∈ (prog I).funcs, ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i)) :
    ¬ TlsSecond I h (Arm.r .PC (runX ((sys I B).mach M' h) N (enterAt (art I h) m))) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hFh := hF h hh
  cases N with
  | zero => exact not_tlsSecond_base hFh (hT h hh) ⟨rl, hrl, ht, (pc_enterAt (art I h) m).symm.trans he⟩
  | succ N1 =>
  have hpc1 := hrun' _ _ _
    (ReachN.act (k := N1) fun j hj => fun hr => hmin j (by omega) (returned_iff.2 hr))
    (by rw [← runX_succ' ((sys I B).mach M' h)]; exact hN.2.1) rl hrl ht
    (by rw [← runX_succ' ((sys I B).mach M' h) N1]; exact he)
  -- the call's word is the callee's TLSDESC `adrp`
  have hpcm : Arm.r .PC m = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC m + 4 = wAt (art I h) rl.offset + 4 := by rw [← hN.1, he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  obtain ⟨j, t, hj, ho, -⟩ := tls_lines hFh (hT h hh) hrl ht
  have hs1 := hsite h hh _ _ (insnAt_of_line hFh hj)
  rw [ho] at hs1
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨i0, hi0, hs0, -⟩ := hok0.site
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hi0
  have hb := progBase_of (hF g hg) hm hok0.program hj0
  simp only [CallsAt, hb] at hc
  rw [hpcm, hs1] at hs0
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩ <;> rw [hins] at hi0 <;> cases hi0
  · simp [siteOf, hn] at hs0
  · simp [siteOf] at hs0

theorem act_coreT (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : ∀ g ∈ (prog I).funcs, TlsClosed (art I g).fa.lines.toList)
    (hsite : ∀ g ∈ (prog I).funcs, ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i))
    (hcallT : ∀ d s, Arm.r .TPIDR (B.hooks.call d s) = Arm.r .TPIDR s)
    (haddr : ∀ g ∈ (prog I).funcs, ∀ rl ∈ (art I g).fb.relocs, rl.type = .tlsDescAdrPage21 →
      B.tp + tpOffOf I file rl.sym = I.symAddr rl.sym 0) (M : Nat)
    (hcall : ∀ M', M = M' + 1 → ActSimT I B file M') : ActSimT I B file M := by
  intro g c e hg hpc hsim hrun htls htp k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hret hsec hsecT herr
  have hFg := hF g hg
  have hok : ∀ j, (∀ j' ≤ j, ¬ Returned (art I g) c
        (runX ((sys I (leBase I B file)).mach M g) j' c)) →
      Arm.r .ERR (runX ((sys I (leBase I B file)).mach M g) (j + 1) c) = .None →
      StepOk I (leBase I B file) file M g (runX ((sys I (leBase I B file)).mach M g) j c) :=
    fun j hj he => hrun _ _ _ (ReachN.act hj)
      (by rw [← runX_succ' ((sys I (leBase I B file)).mach M g)]; exact he)
  have htp' : ∀ j, Arm.r .TPIDR (runX ((sys I (leBase I B file)).mach M g) j c) = B.tp :=
    fun j => (runX_tpidr (mach_le_tpidr hcallT M g) j c).trans htp
  cases k with
  | zero => exact ⟨0, hsim⟩
  | succ k0 =>
  have hok0 : StepOk I (leBase I B file) file M g (runX ((sys I (leBase I B file)).mach M g) k0 c) :=
    hok k0 (fun j hj => hret j (by omega)) herr
  rw [runX_succ'] at hsec hsecT herr ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k0 c))
  · -- the second word of a pair: two steps from its first word
    obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    have hok1 : StepOk I (leBase I B file) file M g (runX ((sys I (leBase I B file)).mach M g) k1 c) :=
      hok k1 (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := hok1.cf rl hrl ht
      (by rw [← runX_succ' ((sys I (leBase I B file)).mach M g) k1]; exact he)
    have hns1 := first_not_second hFg hrl ht
    obtain ⟨k', hk'⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact hns1)
      (fun hT1 => by
        rw [hpc1] at hT1
        obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFg.layout rl).1 hrl
        have h0 := insnAt_of_line hFg hj
        rw [ho] at h0
        obtain ⟨tmp, n, rfl⟩ := tlsSecond_insn hFg (hT g hg) hT1 h0
        rcases ht with h | h <;> rw [h] at hi <;> simp [Insn.reloc?] at hi)
      hok1.err
    refine ⟨k' + 2, ?_⟩
    -- both steps are real sites
    obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFg.layout rl).1 hrl
    have hins1 : insnAt (art I g).fa (art I g).base
        (Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k1 c)) = some i := by
      rw [hpc1, ← ho]; exact insnAt_of_line hFg hj
    have hA := stepT_of_ins hok1 (hk'.1 .PC) hins1 (Insn.tlsSite_of_reloc hi ht)
    obtain ⟨i0, hins0, -, -⟩ := hok0.site
    obtain ⟨hpcE, -⟩ := pair_first_pc hFg hrl ht hpc1 hok1 hk'
    have hB := stepT_of_ins (I := I) (B := B) (file := file)
      (e := step I (leBase I B file) file (runX (stepT I B file) k' e)) hok0
      (hpcE.symm.trans (congrArg (Arm.r .PC)
        (runX_succ' ((sys I (leBase I B file)).mach M g) k1 c).symm))
      hins0 (second_insn hFg ⟨rl, hrl, ht, he⟩ hins0)
    rw [runX_succ' ((sys I (leBase I B file)).mach M g) k1, runX_add (stepT I B file) k' 2]
    show Sim I _ (stepT I B file (stepT I B file (runX (stepT I B file) k' e)))
    rw [hA, hB]
    exact pair_step hFg hrl ht hpc1 hok1
      (by rw [← runX_succ' ((sys I (leBase I B file)).mach M g) k1]; exact hok0) hk'
  by_cases hsT : TlsSecond I g (Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k0 c))
  · -- the TLSDESC `ldr` word: two model steps, six processor steps from the `adrp`
    obtain ⟨rl, hrl, ht, he⟩ := hsT
    cases k0 with
    | zero => exact (not_tlsSecond_base hFg (hT g hg) ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    have hok1 : StepOk I (leBase I B file) file M g (runX ((sys I (leBase I B file)).mach M g) k1 c) :=
      hok k1 (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := htls _ _ _ (ReachN.act (k := k1) fun j hj => hret j (by omega))
      (by rw [← runX_succ' ((sys I (leBase I B file)).mach M g)]; exact hok0.err) rl hrl ht
      (by rw [← runX_succ' ((sys I (leBase I B file)).mach M g) k1]; exact he)
    obtain ⟨hn1, hn2⟩ := tlsFirst_not hFg (hT g hg) hrl ht
    obtain ⟨k', hk'⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact hn1) (by rw [hpc1]; exact hn2) hok1.err
    refine ⟨k' + 6, ?_⟩
    rw [runX_succ' ((sys I (leBase I B file)).mach M g) k1, runX_add (stepT I B file) k' 6]
    exact tls_step hFg (hT g hg) (hsite g hg) hrl ht hpc1 hok1.err hok1.program hk' (htp' k1)
      (haddr g hg rl hrl ht)
  obtain ⟨k', hk'⟩ := ih k0 (by omega) (fun j hj => hret j (by omega)) hs hsT hok0.err
  obtain ⟨i, hins, -, -⟩ := hok0.site
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
  have hb := progBase_of hFg hm hok0.program hj0
  have hpe : Arm.r .PC (runX (stepT I B file) k' e) =
      Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k0 c) := hk'.1 .PC
  -- a call of a function of the program
  have hprog : ∀ h, CallsAt I (leBase I B file) g (runX ((sys I (leBase I B file)).mach M g) k0 c) h →
      i.tlsSite = false →
      ∃ k'', Sim I ((sys I (leBase I B file)).mach M g (runX ((sys I (leBase I B file)).mach M g) k0 c))
        (runX (stepT I B file) k'' e) := by
    intro h hc hti
    have hh := callee_mem hc
    have hstT := stepT_of_ins hok0 hpe hins hti
    rw [mach_call hc] at herr ⊢
    cases M with
    | zero => exact absurd herr (junkAt_err _)
    | succ M' =>
    have hrun' : RunOkSN I (leBase I B file) file M' h
        (enterAt (art I h) (runX ((sys I (leBase I B file)).mach (M' + 1) g) k0 c)) :=
      fun M'' g' t hr he => hrun _ _ _ (ReachN.nest (fun j hj => hret j (by omega)) hc
        (by rw [runX_succ', mach_call hc]; exact herr) hr) he
    have htls' : RunTlsN I (leBase I B file) M' h
        (enterAt (art I h) (runX ((sys I (leBase I B file)).mach (M' + 1) g) k0 c)) :=
      fun M'' g' t hr he => htls _ _ _ (ReachN.nest (fun j hj => hret j (by omega)) hc
        (by rw [runX_succ', mach_call hc]; exact herr) hr) he
    simp only [LinkSys.pcall] at herr ⊢
    have hent := call_enter hFg (hF h hh) hok0 hk' hc
    unfold linkedCall at herr ⊢
    split
    · rename_i hex
      obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
      have htpc : Arm.r .TPIDR
          (enterAt (art I h) (runX ((sys I (leBase I B file)).mach (M' + 1) g) k0 c)) = B.tp := by
        simp only [enterAt, r_set_program, Arm.r_of_w_different (show Arm.StateField.TPIDR ≠ .PC by simp),
          Arm.r_of_w_different (show Arm.StateField.TPIDR ≠ .GPR 30#5 by simp)]
        exact htp' k0
      obtain ⟨k2, hk2⟩ := hcall M' rfl h _ _ hh (pc_enterAt _ _) hent hrun' htls' htpc _
        (fun j hj hr => hmin j hj (returned_iff.2 hr))
        (ret_not_secondN hF hg hh hok0 hc hrun' hN hmin)
        (ret_not_tlsSecondN hF hT hg hh hok0 hc htls' hN hmin hsite) hN.2.1
      refine ⟨k' + 1 + k2, ?_⟩
      rw [runX_add, runX_add]
      show Sim I _ (runX (stepT I B file) k2 (stepT I B file (runX (stepT I B file) k' e)))
      rw [hstT]
      exact sim_set_program _ hk2
    · simp [‹¬ _›, junkAt, Arm.r_of_w_same] at herr
  by_cases hhk : i.hooked = false
  · refine ⟨k' + 1, ?_⟩
    rw [runX_succ', stepT_of_ins hok0 hpe hins (Insn.tlsSite_of_hooked hhk)]
    exact plain_step hFg hok0 hk' hins hhk
  · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
    case bl n =>
      cases hn : (prog I).func? n with
      | none =>
        refine ⟨k' + 1, ?_⟩
        rw [runX_succ', stepT_of_ins hok0 hpe hins rfl]
        exact hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩)
      | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩) rfl
    case blr x =>
      cases hn : (blrTarget (runX ((sys I (leBase I B file)).mach M g) k0 c)).bind
          (symCallee (sys I (leBase I B file)).Xb (prog I)) with
      | none =>
        refine ⟨k' + 1, ?_⟩
        rw [runX_succ', stepT_of_ins hok0 hpe hins rfl]
        exact hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩))
      | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩) rfl
    case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
    case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
    case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
    case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
    case adrpTlsDesc a b => exact absurd (tls_lands hFg hok0 hins) hsecT
    case ldrTlsDescLo12 a b d => exact absurd (tlsSecond_of_ldr hFg hins) hsT

end Core

/-- **The simulation by the hook-free machine at every depth.** -/
theorem act_simT {I : LinkInput} {B : BaseEnv} {file : ByteArray}
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : ∀ g ∈ (prog I).funcs, TlsClosed (art I g).fa.lines.toList)
    (hsite : ∀ g ∈ (prog I).funcs, ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i))
    (hcallT : ∀ d s, Arm.r .TPIDR (B.hooks.call d s) = Arm.r .TPIDR s)
    (haddr : ∀ g ∈ (prog I).funcs, ∀ rl ∈ (art I g).fb.relocs, rl.type = .tlsDescAdrPage21 →
      B.tp + tpOffOf I file rl.sym = I.symAddr rl.sym 0) : ∀ M, ActSimT I B file M
  | 0 => act_coreT hF hT hsite hcallT haddr 0 fun _ h => by cases h
  | M + 1 => act_coreT hF hT hsite hcallT haddr (M + 1) fun M' h => by
    obtain rfl : M = M' := Nat.succ.inj h
    exact act_simT hF hT hsite hcallT haddr M

/-! ## The theorem about the executable -/

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The model's outcome transfers to the hook-free machine** (`exec_of_modelN` for `stepT`). -/
theorem exec_of_modelT (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : ∀ g ∈ (prog I).funcs, TlsClosed (art I g).fa.lines.toList)
    (hsite : ∀ g ∈ (prog I).funcs, ∀ a i, insnAt (art I g).fa (art I g).base a = some i →
      siteAt I a = some (siteOf (prog I) i))
    {r : Arm.ArmState} (hL : TlsLoader I B file r)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a)
    (hrun : RunOkSN I (leBase I B file) file M f (modelOf I f r))
    (htls : RunTlsN I (leBase I B file) M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefines (art I f).fb (art I f).base (xreg 30 r)
      ((sys I (leBase I B file)).mach M f) (modelOf I f r) o) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hsimN := act_simT hF hT hsite hL.call hL.addr M f _ r hf hpc' hsim hrun htls
    (by rw [r_modelOf]; exact hL.tp)
  have hcode : ∀ a, Arm.r .PC a = xreg 30 r → ¬ Second I f (Arm.r .PC a) ∧ ¬ TlsSecond I f (Arm.r .PC a) :=
    fun a ha => ⟨fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, ha]), fun hs => by
      obtain ⟨k, hk, he⟩ := tlsSecond_code hFf (hT f hf) hs
      exact hra k hk (by rw [← he, ha])⟩
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (hcode _ hret.pc).1
      (hcode _ hret.pc).2 hret.err
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v hv => ?_, fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · simp only [xreg]; rw [hk'.1]; exact hx j v hv
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (stepT I B file) k' r).mem =
        (runX (stepT I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_return (B := leBase I B file) hFf hra' htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((sys I (leBase I B file)).mach M f) n (modelOf I f r)))
    · -- a trap at a second word: one executable step after the first word
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I (leBase I B file)).mach M f)]; exact htrap.err)
      have hpc1 := hok1.cf rl hrl ht
        (by rw [← runX_succ' ((sys I (leBase I B file)).mach M f) n1]; exact he)
      obtain ⟨hn1, hn2⟩ : ¬ Second I f (wAt (art I f) rl.offset) ∧
          ¬ TlsSecond I f (wAt (art I f) rl.offset) := by
        refine ⟨first_not_second hFf hrl ht, fun hT1 => ?_⟩
        obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFf.layout rl).1 hrl
        have h0 := insnAt_of_line hFf hj
        rw [ho] at h0
        obtain ⟨tmp, n, rfl⟩ := tlsSecond_insn hFf (hT f hf) hT1 h0
        rcases ht with h | h <;> rw [h] at hi <;> simp [Insn.reloc?] at hi
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact hn1) (by rw [hpc1]; exact hn2) hok1.err
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hok1 hk'
      obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFf.layout rl).1 hrl
      have hins1 : insnAt (art I f).fa (art I f).base
          (Arm.r .PC (runX ((sys I (leBase I B file)).mach M f) n1 (modelOf I f r))) = some i := by
        rw [hpc1, ← ho]; exact insnAt_of_line hFf hj
      have hA := stepT_of_ins hok1 (hk'.1 .PC) hins1 (Insn.tlsSite_of_reloc hi ht)
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      rw [hA]
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    by_cases hsT : TlsSecond I f (Arm.r .PC (runX ((sys I (leBase I B file)).mach M f) n (modelOf I f r)))
    · -- a trap at a TLSDESC `ldr` word: one executable step after the `adrp`
      obtain ⟨rl, hrl, ht, he⟩ := hsT
      cases n with
      | zero => exact (not_tlsSecond_base hFf (hT f hf) ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I (leBase I B file)).mach M f)]; exact htrap.err)
      have hpc1 := htls _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I (leBase I B file)).mach M f)]; exact htrap.err) rl hrl ht
        (by rw [← runX_succ' ((sys I (leBase I B file)).mach M f) n1]; exact he)
      obtain ⟨hn1, hn2⟩ := tlsFirst_not hFf (hT f hf) hrl ht
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact hn1) (by rw [hpc1]; exact hn2) hok1.err
      obtain ⟨hpcE, herrE⟩ := tls_first_pc (M := M) hFf (hT f hf) (hsite f hf) hrl ht hpc1 hok1.err
        hok1.program hk'
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hsimN n hguard hs hsT htrap.err
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial

end Transfer

end E2E.ExecBytes
