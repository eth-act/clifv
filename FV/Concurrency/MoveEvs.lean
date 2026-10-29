import FV.E2E.MoveReads
import FV.Concurrency.VCodeAddr

/-!
# The memory events of move code (T2k, #311, layer 4b)

The register allocator's moves (`RAFrame.moveInsts`) access only the activation's frame:

* `moveLines_evs`: every Arm memory event of a checked move's lines (`VCodeThread.linesEvs`) is
  at a live frame slot (`sp + off`, directly or through `x16 = sp + off` beyond 32 KiB) or at the
  float-move scratch slot, so in the frame addresses `F` (`FrameOk.inF`, `FrameOk.tmpF`);
* `moveLines_noStx`: no line of a move is a store exclusive (moves are `mov`, `movz`/`movk`/`add`
  and plain single-register loads/stores).

The event addresses of the one-line move instructions, run in sequence (`ExecAll`), are collected
by `InstsEvs`/`linesEvs_of_insts` (as `InstsReads`/`linesReads_of_insts` for the reads).
-/

namespace Backend.Proof

open Backend E2E Concurrency

/-! ## Events of runs of lines -/

theorem mv_linesEvs_nil {env : Env} {ls : List Line} (s : Arm.ArmState)
    (h : Concurrency.Code.kinds ls = []) : VCodeThread.linesEvs env ls s = [] := by
  have := VCodeEvents.linesEvs_kinds env ls s
  rw [h] at this
  exact List.map_eq_nil_iff.1 (List.eq_nil_of_sublist_nil this)

/-- Running one line that runs to `t0`: its events, then the rest's from `t0`. -/
theorem mv_linesEvs_cons {env : Env} {x : Insn} {t : Option Clif.TrapCode} {s t0 : Arm.ArmState}
    (h : execLines env [.ins x t] s = some t0) (ls : List Line) :
    VCodeThread.linesEvs env (.ins x t :: ls) s =
      VCodeThread.linesEvs env [.ins x t] s ++
        VCodeThread.linesEvs { env with pc := env.pc + 4 } ls t0 := by
  simp only [execLines] at h
  split at h
  · rename_i ai ha
    split at h
    · rename_i hpc
      simp only [Option.some.injEq] at h
      subst h
      simp only [VCodeThread.linesEvs, ha, hpc, ite_true, List.append_nil]
    · cases h
  · cases h

/-- The event addresses of a list of allocated instructions run in sequence from `s` (`ExecAll`):
each instruction's lines, from the state the instructions before it reach, have their events'
addresses in `P`. -/
def InstsEvs (ctx : FnCtx) (is : List MInst) (s : Arm.ArmState) (P : BitVec 64 → Prop) : Prop :=
  ∀ k i t, is[k]? = some i → ExecAll ctx (is.take k) s t → ∀ ls ps',
    i.lines ctx {} = .ok (ls, ps') → ∀ env, ∀ e ∈ VCodeThread.linesEvs env ls t, P e.addr

theorem InstsEvs.mono {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState} {P Q : BitVec 64 → Prop}
    (h : InstsEvs ctx is s P) (hPQ : ∀ a, P a → Q a) : InstsEvs ctx is s Q :=
  fun k i t hk ht ls ps' hl env e he => hPQ _ (h k i t hk ht ls ps' hl env e he)

/-- Instructions whose lines have no memory kinds have no events. -/
theorem instsEvs_noKinds {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ i ∈ is, ∀ ls ps', i.lines ctx {} = .ok (ls, ps') → Concurrency.Code.kinds ls = []) :
    InstsEvs ctx is s P := fun _ i t hk _ ls ps' hl env e he => by
  rw [mv_linesEvs_nil t (h i (List.mem_of_getElem? hk) ls ps' hl)] at he
  cases he

theorem instsEvs_append {ctx : FnCtx} {A B : List MInst} {s s1 : Arm.ArmState}
    {P : BitVec 64 → Prop} (hA : InstsEvs ctx A s P) (hex : ExecAll ctx A s s1)
    (hB : InstsEvs ctx B s1 P) : InstsEvs ctx (A ++ B) s P := by
  intro k i t hk ht ls ps' hl env
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at ht
    exact hA k i t hk ht ls ps' hl env
  · rw [List.getElem?_append_right hge] at hk
    rw [List.take_append, List.take_of_length_le hge] at ht
    obtain ⟨m, h1, h2⟩ := ExecAll.split ht
    obtain rfl := ExecAll.det h1 hex
    exact hB _ i t hk h2 ls ps' hl env

/-- A single instruction. -/
theorem instsEvs_single {ctx : FnCtx} {i : MInst} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ ls ps', i.lines ctx {} = .ok (ls, ps') → ∀ env,
      ∀ e ∈ VCodeThread.linesEvs env ls s, P e.addr) :
    InstsEvs ctx [i] s P := by
  intro k i' t hk ht ls ps' hl env
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [List.take_zero, ExecAll] at ht
    subst ht
    exact h ls ps' hl env
  | succ k => simp at hk

/-- **The lines of one-line instructions run in sequence** have the events the instructions
have. -/
theorem linesEvs_of_insts (ctx : FnCtx) (af : AFunc) {P : BitVec 64 → Prop} :
    ∀ (is : List MInst) (s s' : Arm.ArmState), (∀ i ∈ is, OneLine ctx i) → ExecAll ctx is s s' →
      InstsEvs ctx is s P → ∀ ls ps ps', codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps') →
      ∀ env, ∀ e ∈ VCodeThread.linesEvs env ls s, P e.addr
  | [], s, s', _, _, _, ls, ps, ps', hc, env => by
    simp only [List.map_nil, codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    intro e he; simp [VCodeThread.linesEvs] at he
  | i :: is, s, s', hone, hex, hev, ls, ps, ps', hc, env => by
    obtain ⟨t0, hex0, hte, htp, hrest⟩ := hex
    obtain ⟨x, t, hl, -, -⟩ := hone i (by simp)
    simp only [List.map_cons, codeLinesE, ainstLines, hl, bind, Except.bind] at hc
    split at hc
    · cases hc
    rename_i r hr
    obtain ⟨ls2, ps2⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.singleton_append] at hc
    obtain ⟨rfl, -⟩ := hc
    have h1 : execLines env [.ins x t] s = some t0 := by
      have := hex0 env
      simp only [execMInst, hl] at this
      exact this
    have hev' : InstsEvs ctx is t0 P := fun k j u hk hu ls ps' hl' env =>
      hev (k + 1) j u (by simpa using hk) ⟨t0, hex0, hte, htp, by simpa using hu⟩ ls ps' hl' env
    have ih := linesEvs_of_insts ctx af is t0 s' (fun j hj => hone j (by simp [hj])) hrest hev'
      ls2 _ _ hr
    rw [mv_linesEvs_cons h1]
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hev 0 i s rfl rfl _ _ (hl {}) env e he
    · exact ih _ e he

/-! ## 128-bit slot accesses -/

theorem evs_unsc128 {opc : BitVec 2} {imm9 : BitVec 9} {Rn Rt : BitVec 5} {s : Arm.ArmState} :
    ∀ e ∈ ArmInstFoot.instEvs (.LDST (.Reg_unscaled_imm
      { size := 0#2, VR := 1#1, opc := opc, imm9 := imm9, Rn := Rn, Rt := Rt })) s,
      e.addr = Arm.read_gpr 64 Rn s + BitVec.signExtend 64 imm9 := by
  intro e he
  simp only [ArmInstFoot.instEvs, ite_true, ArmInstFoot.ldsturEvs] at he
  split at he
  · cases he
  split at he
  · cases he
  split at he <;> simp only [List.mem_singleton] at he <;> subst he <;> rfl

theorem evs_uimm128 {opc : BitVec 2} (hopc : opc = 2#2 ∨ opc = 3#2) {imm12 : BitVec 12}
    {Rn Rt : BitVec 5} {s : Arm.ArmState} :
    ∀ e ∈ ArmInstFoot.instEvs (.LDST (.Reg_unsigned_imm
      { size := 0#2, V := 1#1, opc := opc, imm12 := imm12, Rn := Rn, Rt := Rt })) s,
      e.addr = Arm.read_gpr 64 Rn s + (BitVec.setWidth 64 imm12 <<< 4) := by
  intro e he
  rcases hopc with rfl | rfl <;>
  · simp (config := {decide := true}) only [ArmInstFoot.instEvs, ArmInstFoot.immEvs] at he
    simp (config := {decide := true}) at he
    obtain ⟨-, -, rfl⟩ := he
    simp (config := {decide := true}) only [Arm.LDST.Reg_offset.value]
    rfl

/-- The events of a 128-bit store at an immediate final mode: at the mode's address. -/
theorem st128_evs (ctx : FnCtx) (env : Env) {n : Nat} (hn : n < 32) {m : AMode} (hm : FinalAM 16 m)
    (hk : (∃ B k, m = .unscaled B k) ∨ ∃ B k, m = .unsignedOffset B k) (t : Arm.ArmState)
    {ai : Arm.ArmInst} (ha : Insn.toArmInst env (.store .fpuStore128 (.v n) m) = .ok ai) :
    ∀ e ∈ ArmInstFoot.instEvs ai t, e.addr = m.addr ctx 16 t := by
  rcases hk with ⟨B, k, rfl⟩ | ⟨B, k, rfl⟩
  · obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb t
    have e : Insn.toArmInst env (.store .fpuStore128 (.v n) (.unscaled B k)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 2#2, imm9 := BitVec.ofInt 9 k, Rn := Rn, Rt := BitVec.ofNat 5 n })) := by
      clear ha
      simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, encV_v' hn, sField,
        Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure] <;> rfl
    rw [e] at ha; cases ha
    intro ev hev
    rw [evs_unsc128 ev hev, hr, simm9_value k h1 h2]
    rfl
  · obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb t
    have e : Insn.toArmInst env (.store .fpuStore128 (.v n) (.unsignedOffset B k)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 2#2, imm12 := BitVec.ofNat 12 (k / 16), Rn := Rn, Rt := BitVec.ofNat 5 n })) := by
      clear ha
      simp_all [Insn.toArmInst, Insn.armFields, StoreOp.fields, ldstFields, encV_v' hn, uField,
        Arm.ArmInst.norm, StoreOp.bytes, bind, Except.bind, pure, Except.pure] <;> rfl
    rw [e] at ha; cases ha
    intro ev hev
    rw [evs_uimm128 (.inl rfl) ev hev, hr, ldst_offset16 k h1 h2]
    rfl

/-- The events of a 128-bit load at an immediate final mode: at the mode's address. -/
theorem ld128_evs (ctx : FnCtx) (env : Env) {n : Nat} (hn : n < 32) {m : AMode} (hm : FinalAM 16 m)
    (hk : (∃ B k, m = .unscaled B k) ∨ ∃ B k, m = .unsignedOffset B k) (t : Arm.ArmState)
    {ai : Arm.ArmInst} (ha : Insn.toArmInst env (.load .fpuLoad128 (.v n) m) = .ok ai) :
    ∀ e ∈ ArmInstFoot.instEvs ai t, e.addr = m.addr ctx 16 t := by
  rcases hk with ⟨B, k, rfl⟩ | ⟨B, k, rfl⟩
  · obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb t
    have e : Insn.toArmInst env (.load .fpuLoad128 (.v n) (.unscaled B k)) =
        .ok (.LDST (.Reg_unscaled_imm { size := 0#2, VR := 1#1, opc := 3#2, imm9 := BitVec.ofInt 9 k, Rn := Rn, Rt := BitVec.ofNat 5 n })) := by
      clear ha
      simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, encV_v' hn, sField,
        Arm.ArmInst.norm, bind, Except.bind, pure, Except.pure] <;> rfl
    rw [e] at ha; cases ha
    intro ev hev
    rw [evs_unsc128 ev hev, hr, simm9_value k h1 h2]
    rfl
  · obtain ⟨hb, h1, h2⟩ := hm
    obtain ⟨Rn, hRn, hr, -⟩ := enc_base hb t
    have e : Insn.toArmInst env (.load .fpuLoad128 (.v n) (.unsignedOffset B k)) =
        .ok (.LDST (.Reg_unsigned_imm { size := 0#2, V := 1#1, opc := 3#2, imm12 := BitVec.ofNat 12 (k / 16), Rn := Rn, Rt := BitVec.ofNat 5 n })) := by
      clear ha
      simp_all [Insn.toArmInst, Insn.armFields, LoadOp.fields, ldstFields, encV_v' hn, uField,
        Arm.ArmInst.norm, LoadOp.bytes, bind, Except.bind, pure, Except.pure] <;> rfl
    rw [e] at ha; cases ha
    intro ev hev
    rw [evs_uimm128 (.inr rfl) ev hev, hr, ldst_offset16 k h1 h2]
    rfl

/-- The events of one line, from its instruction's events (no events when it does not encode). -/
theorem mv_single {env : Env} {x : Insn} {tc : Option Clif.TrapCode} {s : Arm.ArmState}
    {P : BitVec 64 → Prop}
    (h : ∀ ai, x.toArmInst env = .ok ai → ∀ e ∈ ArmInstFoot.instEvs ai s, P e.addr) :
    ∀ e ∈ VCodeThread.linesEvs env [.ins x tc] s, P e.addr := by
  cases ha : x.toArmInst env with
  | error _ => simp only [VCodeThread.linesEvs, ha]; exact fun _ h => nomatch h
  | ok ai => rw [VCodeAddr.linesEvs_single ha]; exact h ai ha

/-- The final mode of a 128-bit slot access at `sp + off` (aligned, below 32 KiB). -/
theorem memFinalize_sp128 (ctx : FnCtx) {off : Nat} (h16 : off % 16 = 0) (hoff : off < 32768) :
    ∃ m', memFinalize ctx (.spOffset off) 16 = .ok ([], m') ∧ FinalAM 16 m' ∧
      ((∃ B k, m' = .unscaled B k) ∨ ∃ B k, m' = .unsignedOffset B k) ∧
      ∀ t, m'.addr ctx 16 t = spOf t + BitVec.ofNat 64 off := by
  by_cases h9 : off ≤ 255
  · refine ⟨.unscaled .sp off, ?_, ⟨trivial, by omega, by omega⟩, .inl ⟨_, _, rfl⟩,
      fun t => by simp [AMode.addr, regX]⟩
    simp only [memFinalize, pure, Except.pure]
    rw [show simm9? (off : Int) = some (off : Int) by simp [simm9?]; omega]
  · refine ⟨.unsignedOffset .sp off, ?_, ⟨trivial, h16, by omega⟩, .inr ⟨_, _, rfl⟩,
      fun t => by simp [AMode.addr, regX]⟩
    simp only [memFinalize, pure, Except.pure]
    rw [show simm9? (off : Int) = none by simp [simm9?]; omega,
      show uimm12Scaled? (off : Int) 16 = some off by simp [uimm12Scaled?]; omega]

/-- The events of a 128-bit store's lines at a mode `memFinalize` keeps immediate. -/
theorem st128_lines_evs (ctx : FnCtx) (env : Env) {n : Nat} (hn : n < 32) {m m' : AMode}
    {fl : Clif.MemFlags} (hf : memFinalize ctx m 16 = .ok ([], m')) (hm : FinalAM 16 m')
    (hk : (∃ B k, m' = .unscaled B k) ∨ ∃ B k, m' = .unsignedOffset B k) {ls : List Line}
    {ps' : PState} (hl : MInst.lines ctx (.store .fpuStore128 (.v n) m fl) {} = .ok (ls, ps'))
    (t : Arm.ArmState) : ∀ e ∈ VCodeThread.linesEvs env ls t, e.addr = m'.addr ctx 16 t := by
  simp only [MInst.lines, StoreOp.bytes, hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq, List.nil_append] at hl
  obtain ⟨rfl, -⟩ := hl
  exact mv_single (P := (· = m'.addr ctx 16 t)) fun ai ha => st128_evs ctx env hn hm hk t ha

/-- The events of a 128-bit load's lines at a mode `memFinalize` keeps immediate. -/
theorem ld128_lines_evs (ctx : FnCtx) (env : Env) {n : Nat} (hn : n < 32) {m m' : AMode}
    {fl : Clif.MemFlags} (hf : memFinalize ctx m 16 = .ok ([], m')) (hm : FinalAM 16 m')
    (hk : (∃ B k, m' = .unscaled B k) ∨ ∃ B k, m' = .unsignedOffset B k) {ls : List Line}
    {ps' : PState} (hl : MInst.lines ctx (.load .fpuLoad128 (.v n) m fl) {} = .ok (ls, ps'))
    (t : Arm.ArmState) : ∀ e ∈ VCodeThread.linesEvs env ls t, e.addr = m'.addr ctx 16 t := by
  simp only [MInst.lines, LoadOp.bytes, hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq, List.nil_append] at hl
  obtain ⟨rfl, -⟩ := hl
  exact mv_single (P := (· = m'.addr ctx 16 t)) fun ai ha => ld128_evs ctx env hn hm hk t ha

/-! ## Slot stores and loads -/

/-- A register of class `cls` the slot code encodes. -/
def ClsReg : RegClass → Reg → Prop
  | .int, r => ∃ n, r = .x n ∧ n ≤ 30
  | .float, r => ∃ n, r = .v n ∧ n < 32

theorem clsReg_of {r : Reg} {cls : RegClass} (hc : r.realClass? = some cls)
    (ha : r.allocatable = true) : ClsReg cls r := by
  rcases allocatable_cases ha with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, hn⟩ <;>
    cases cls <;> simp_all [Reg.realClass?, ClsReg] <;> omega

theorem spAddrX16_kinds (ctx : FnCtx) (off : Nat) :
    ∀ i ∈ spAddrX16 off, ∀ ls ps', i.lines ctx {} = .ok (ls, ps') →
      Concurrency.Code.kinds ls = [] := by
  intro i hi ls ps' hl
  simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hi
  rcases hi with (rfl | ⟨p, -, rfl⟩) | rfl <;>
  · simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rfl

theorem x16_after (s : Arm.ArmState) (P X : BitVec 64) :
    Arm.r (.GPR (rnum 16)) (pcx s 16 P X) = X := (pcx_facts s 16 P X).2.2.2

/-- **The events of a slot store** `slotStoreAt cls r off` from `s`: at `sp + off`. -/
theorem slotStoreAt_evs (ctx : FnCtx) {cls : RegClass} {r : Reg} {off : Nat} (hr : ClsReg cls r)
    (h16 : cls = .float → off % 16 = 0) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    InstsEvs ctx (slotStoreAt cls r off) s (· = spOf s + BitVec.ofNat 64 off) := by
  unfold slotStoreAt
  split
  · rename_i hlt
    refine instsEvs_single fun ls ps' hl env e he => ?_
    cases cls with
    | int =>
      obtain ⟨n, rfl, hn⟩ := hr
      have := VCodeAddr.store_lines_evs ctx env .store64 (fun h => by cases h) hn
        (m := .spOffset off) trustedFlags trivial s halign hl e he
      rw [this.2.1]; simp [AMode.addr]
    | float =>
      obtain ⟨n, rfl, hn⟩ := hr
      obtain ⟨m', hf, hm, hk, ha⟩ := memFinalize_sp128 ctx (h16 rfl) hlt
      rw [st128_lines_evs ctx env hn hf hm hk hl s e he, ha]
  · obtain ⟨P, hx⟩ := execAll_spAddrX16 ctx off s
    refine instsEvs_append (instsEvs_noKinds (spAddrX16_kinds ctx off)) hx
      (instsEvs_single fun ls ps' hl env e he => ?_)
    have hfin : ∀ b, 0 < b → b ∣ 16 → FinalAM b (.unsignedOffset (.x 16) 0) := fun b hb _ =>
      ⟨by simp [BaseOk], by simp, by simp⟩
    cases cls with
    | int =>
      obtain ⟨n, rfl, hn⟩ := hr
      have := VCodeAddr.store_lines_evs ctx env .store64 (fun h => by cases h) hn
        (m := .unsignedOffset (.x 16) 0) trustedFlags (hfin 8 (by decide) (by decide)) _
        (pcx_align halign _ _) hl e he
      rw [this.2.1]
      simp only [AMode.addr, regX, x16_after]; simp
    | float =>
      obtain ⟨n, rfl, hn⟩ := hr
      rw [st128_lines_evs ctx env hn (memFinalize_final ctx 16 (hfin 16 (by decide) (by decide)))
        (hfin 16 (by decide) (by decide)) (.inr ⟨_, _, rfl⟩) hl _ e he]
      simp only [AMode.addr, regX, x16_after]; simp

/-- **The events of a slot load** `slotLoadAt cls r off` from `s`: at `sp + off`. -/
theorem slotLoadAt_evs (ctx : FnCtx) {cls : RegClass} {r : Reg} {off : Nat} (hr : ClsReg cls r)
    (h16 : cls = .float → off % 16 = 0) {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    InstsEvs ctx (slotLoadAt cls r off) s (· = spOf s + BitVec.ofNat 64 off) := by
  unfold slotLoadAt
  split
  · rename_i hlt
    refine instsEvs_single fun ls ps' hl env e he => ?_
    cases cls with
    | int =>
      obtain ⟨n, rfl, hn⟩ := hr
      have := VCodeAddr.load_lines_evs ctx env .uload64 (fun h => by cases h) hn
        (m := .spOffset off) trustedFlags trivial s halign hl e he
      rw [this.2.1]; simp [AMode.addr]
    | float =>
      obtain ⟨n, rfl, hn⟩ := hr
      obtain ⟨m', hf, hm, hk, ha⟩ := memFinalize_sp128 ctx (h16 rfl) hlt
      rw [ld128_lines_evs ctx env hn hf hm hk hl s e he, ha]
  · obtain ⟨P, hx⟩ := execAll_spAddrX16 ctx off s
    refine instsEvs_append (instsEvs_noKinds (spAddrX16_kinds ctx off)) hx
      (instsEvs_single fun ls ps' hl env e he => ?_)
    have hfin : ∀ b, 0 < b → b ∣ 16 → FinalAM b (.unsignedOffset (.x 16) 0) := fun b hb _ =>
      ⟨by simp [BaseOk], by simp, by simp⟩
    cases cls with
    | int =>
      obtain ⟨n, rfl, hn⟩ := hr
      have := VCodeAddr.load_lines_evs ctx env .uload64 (fun h => by cases h) hn
        (m := .unsignedOffset (.x 16) 0) trustedFlags (hfin 8 (by decide) (by decide)) _
        (pcx_align halign _ _) hl e he
      rw [this.2.1]
      simp only [AMode.addr, regX, x16_after]; simp
    | float =>
      obtain ⟨n, rfl, hn⟩ := hr
      rw [ld128_lines_evs ctx env hn (memFinalize_final ctx 16 (hfin 16 (by decide) (by decide)))
        (hfin 16 (by decide) (by decide)) (.inr ⟨_, _, rfl⟩) hl _ e he]
      simp only [AMode.addr, regX, x16_after]; simp

theorem align_of_spOf {s t : Arm.ArmState} (h : spOf t = spOf s) (ha : Arm.CheckSPAlignment s) :
    Arm.CheckSPAlignment t := by
  have e : Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s := h
  simp only [Arm.CheckSPAlignment, Arm.read_gpr] at ha ⊢
  rw [e]; exact ha

/-! ## The events of a checked move -/

/-- **The event addresses of move code** (`RAFrame.moveInsts` of a checked move between live
locations), run from `s` with `sp = sp0`: in the frame addresses `F`. -/
theorem moveInsts_evs {vc : VCode} {rf : RFunc} {sp0 : BitVec 64} {F : BitVec 64 → Prop}
    (hfr : FrameOk (RAFrame.compute vc rf) (Live rf) (rf.floatMove = true) sp0 F)
    (ctx : FnCtx) {c : CheckCtx} {wh : String} {src dst : Loc}
    (hchk : c.checkMove wh src dst = .ok ()) (hLs : Live rf src) (hLd : Live rf dst)
    (hT : ∀ a b, src = .reg (.v a) → dst = .reg (.v b) → rf.floatMove = true)
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {s : Arm.ArmState} (hsp : spOf s = sp0) (halign : Arm.CheckSPAlignment s) :
    ∃ is, code = is.map AInst.inst ∧ InstsEvs ctx is s F := by
  subst hsp
  obtain ⟨cls, hcls, hs, hd, hreg⟩ := checkMove_facts hchk
  have hdcls := locOk_cls hd
  have hF : ∀ l o, Live rf l → (RAFrame.compute vc rf).offset l = .ok o →
      ∀ a, a = spOf s + BitVec.ofNat 64 o → F a := fun l o hl ho a ha => by
    have := hfr.inF l o hl ho 0 (by rcases slotBytes_cases l with h | h <;> omega)
    rw [ha]; simpa using this
  cases src with
  | reg a =>
    obtain ⟨hac, haa⟩ := locOk_reg hs
    cases dst with
    | reg b =>
      obtain ⟨hbc, hba⟩ := locOk_reg hd
      cases cls with
      | int =>
        obtain ⟨a', rfl⟩ := reg_int hac
        obtain ⟨b', rfl⟩ := reg_int hbc
        simp only [RAFrame.moveInsts, hac, pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        refine ⟨[.mov .size64 (.x b') (.x a')], rfl, instsEvs_noKinds fun i hi ls ps' hl => ?_⟩
        simp only [List.mem_singleton] at hi
        subst hi
        simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, -⟩ := hl
        simp [Concurrency.Code.kinds, Concurrency.Code.lineKind, Concurrency.Code.insnKind]
      | float =>
        obtain ⟨a', rfl⟩ := reg_float hac
        obtain ⟨b', rfl⟩ := reg_float hbc
        simp only [RAFrame.moveInsts, hac, pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        have hfm := hT a' b' rfl rfl
        rcases allocatable_cases haa with ⟨_, e, _⟩ | ⟨_, e, ha⟩ <;> cases e
        rcases allocatable_cases hba with ⟨_, e, _⟩ | ⟨_, e, hb⟩ <;> cases e
        have hal := (compute_align vc rf).2.2
        have htF : ∀ a, a = spOf s + BitVec.ofNat 64 (RAFrame.compute vc rf).fmoveTmp → F a :=
          fun a h => by rw [h]; simpa using hfr.tmpF hfm 0 (by decide)
        obtain ⟨P, X, hx1⟩ := exec_slotStoreAt_float ctx ha hal halign
        refine ⟨_, rfl, instsEvs_append
          ((slotStoreAt_evs ctx (cls := .float) ⟨a', rfl, ha⟩ (fun _ => hal) halign).mono htF)
          hx1 ?_⟩
        have hsp1 : spOf (stSt (pcx s 16 P X) (RAFrame.compute vc rf).fmoveTmp 16
            (Arm.r (.SFP (rnum a')) (pcx s 16 P X))) = spOf s := by
          simp only [stSt, spOf_write, pcx_sp]
        refine (slotLoadAt_evs ctx (cls := .float) ⟨b', rfl, hb⟩ (fun _ => hal)
          (align_of_spOf hsp1 halign)).mono fun x h => htF x ?_
        rw [h, hsp1]
    | save r => exact hLd.elim
    | stack k cl =>
      simp only [RAFrame.moveInsts, bind, Except.bind] at hmi
      split at hmi
      · cases hmi
      rename_i o hoff
      simp only [pure, Except.pure, Except.ok.injEq] at hmi
      subst hmi
      simp only [hac, Option.getD_some]
      refine ⟨_, rfl, (slotStoreAt_evs ctx (clsReg_of hac haa) (fun e => ?_) halign).mono
        (hF _ o hLd hoff)⟩
      subst e
      have hal := live_align hLd hoff
      rw [slotBytes_float (fun _ h => by cases h) (fun _ h => by cases h) hdcls] at hal
      exact hal.1
  | save r => exact hLs.elim
  | stack k cl =>
    cases dst with
    | stack _ _ | save _ => simp [Loc.isReg] at hreg
    | reg b =>
      obtain ⟨hbc, hba⟩ := locOk_reg hd
      simp only [RAFrame.moveInsts, bind, Except.bind] at hmi
      split at hmi
      · cases hmi
      rename_i o hoff
      simp only [pure, Except.pure, Except.ok.injEq] at hmi
      subst hmi
      simp only [hbc, Option.getD_some]
      refine ⟨_, rfl, (slotLoadAt_evs ctx (clsReg_of hbc hba) (fun e => ?_) halign).mono
        (hF _ o hLs hoff)⟩
      subst e
      have hal := live_align hLs hoff
      rw [slotBytes_float (fun _ h => by cases h) (fun _ h => by cases h) hcls] at hal
      exact hal.1

/-- **Every Arm memory event of a checked move's lines is in the frame** `F`. -/
theorem moveLines_evs {vc : VCode} {rf : RFunc} {sp0 : BitVec 64} {F : BitVec 64 → Prop}
    (hfr : FrameOk (RAFrame.compute vc rf) (Live rf) (rf.floatMove = true) sp0 F)
    (ctx : FnCtx) (af : AFunc) {c : CheckCtx} {wh : String} {src dst : Loc}
    (hchk : c.checkMove wh src dst = .ok ()) (hLs : Live rf src) (hLd : Live rf dst)
    (hT : ∀ a b, src = .reg (.v a) → dst = .reg (.v b) → rf.floatMove = true)
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {s : Arm.ArmState} (hsp : spOf s = sp0) (halign : Arm.CheckSPAlignment s)
    {ls : List Line} {ps ps' : PState} (hls : codeLinesE ctx af code ps = .ok (ls, ps'))
    (env : Env) : ∀ e ∈ VCodeThread.linesEvs env ls s, F e.addr := by
  obtain ⟨-, -, is, s', hcode, hmv, hex, -⟩ :=
    lower_move hfr ctx hchk hLs hLd hT hmi (SameWorld.refl F s) hsp halign
  obtain ⟨is', hcode', hev⟩ := moveInsts_evs hfr ctx hchk hLs hLd hT hmi hsp halign
  obtain rfl : is = is' :=
    (List.map_inj_right (fun _ _ h => AInst.inst.inj h)).1 (hcode.symm.trans hcode')
  subst hcode
  exact linesEvs_of_insts ctx af is s s' (fun i hi => oneLine_of_moveInst ctx (hmv i hi)) hex hev
    ls ps ps' hls env

/-! ## Moves have no store exclusive -/

/-- An exclusive load/store (the only instructions of class `ldx`/`stx`/`ldar`/`stlr`). -/
def isExcl : Arm.ArmInst → Bool
  | .LDST (.Reg_exclusive _) => true
  | _ => false

theorem isExcl_norm (a : Arm.ArmInst) : isExcl a.norm = isExcl a := by
  cases a with
  | LDST i => cases i <;> rfl
  | BR i => cases i <;> rfl
  | DPI i => cases i <;> rfl
  | DPR i => cases i <;> rfl
  | DPSFP i => cases i <;> rfl
  | RES i => cases i <;> rfl

theorem clsOf_ne_stx {a : Arm.ArmInst} (h : isExcl a = false) (rel : Bool) (rs rn : BitVec 5) :
    ArmInstFoot.clsOf a ≠ .stx rel rs rn := by
  cases a with
  | LDST i => cases i <;> simp_all [isExcl, ArmInstFoot.clsOf]
  | BR i =>
    cases i <;> simp only [ArmInstFoot.clsOf] <;> (try split) <;> (try split) <;> simp
  | _ => simp [ArmInstFoot.clsOf]

/-- An instruction without memory kind is no exclusive. -/
theorem isExcl_none {env : Env} {x : Insn} {ai : Arm.ArmInst} (h : x.toArmInst env = .ok ai)
    (hk : Concurrency.Code.insnKind x = none) : isExcl ai = false := by
  unfold Insn.toArmInst at h
  cases ha : x.armFields env with
  | error e => rw [ha] at h; cases h
  | ok a0 =>
    rw [ha] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have hm : VCodeEvents.memCls a0 = false := VCodeEvents.memCls_armFields env x a0 ha hk
    rw [isExcl_norm]
    cases a0 with
    | LDST _ => cases hm
    | _ => rfl

theorem ldstFields_notExcl {size : BitVec 2} {V : BitVec 1} {opc : BitVec 2} {bytes : Nat}
    {Rt : BitVec 5} {m : AMode} {a : Arm.ArmInst} (h : ldstFields size V opc bytes Rt m = .ok a) :
    isExcl a = false := by
  unfold ldstFields at h
  cases m <;> simp only [bind, Except.bind, pure, Except.pure] at h <;> (repeat' split at h) <;>
    (try cases h) <;> rfl

theorem isExcl_store {env : Env} {op : StoreOp} {r : Reg} {m : AMode} {ai : Arm.ArmInst}
    (h : (Insn.store op r m).toArmInst env = .ok ai) : isExcl ai = false := by
  unfold Insn.toArmInst at h
  cases ha : (Insn.store op r m).armFields env with
  | error e => rw [ha] at h; cases h
  | ok a0 =>
    rw [ha] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    rw [isExcl_norm]
    simp only [Insn.armFields, bind, Except.bind] at ha
    repeat' split at ha
    all_goals first | exact ldstFields_notExcl ha | cases ha

theorem isExcl_load {env : Env} {op : LoadOp} {r : Reg} {m : AMode} {ai : Arm.ArmInst}
    (h : (Insn.load op r m).toArmInst env = .ok ai) : isExcl ai = false := by
  unfold Insn.toArmInst at h
  cases ha : (Insn.load op r m).armFields env with
  | error e => rw [ha] at h; cases h
  | ok a0 =>
    rw [ha] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    rw [isExcl_norm]
    simp only [Insn.armFields, bind, Except.bind] at ha
    repeat' split at ha
    all_goals first | exact ldstFields_notExcl ha | cases ha

/-- The instructions of move code (any registers and offsets). -/
def MvShape (i : MInst) : Prop :=
  (∃ sz rd rm, i = .mov sz rd rm) ∨ (∃ op r m fl, i = .store op r m fl) ∨
    (∃ op r m fl, i = .load op r m fl) ∨ (∃ op rd c sz, i = .movWide op rd c sz) ∨
    (∃ rd rn c sz, i = .movK rd rn c sz) ∨
    (∃ op sz rd rn rm e, i = .aluRRRExtend op sz rd rn rm e)

theorem mvShape_spAddrX16 {off : Nat} {i : MInst} (h : i ∈ spAddrX16 off) : MvShape i := by
  simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at h
  rcases h with (rfl | ⟨p, -, rfl⟩) | rfl
  · exact .inr (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, _, _, _, rfl⟩))))

theorem mvShape_slotStoreAt {cls : RegClass} {r : Reg} {off : Nat} {i : MInst}
    (h : i ∈ slotStoreAt cls r off) : MvShape i := by
  unfold slotStoreAt at h
  split at h
  · simp only [List.mem_singleton] at h; subst h
    cases cls <;> exact .inr (.inl ⟨_, _, _, _, rfl⟩)
  · rcases List.mem_append.1 h with h | h
    · exact mvShape_spAddrX16 h
    · simp only [List.mem_singleton] at h; subst h
      cases cls <;> exact .inr (.inl ⟨_, _, _, _, rfl⟩)

theorem mvShape_slotLoadAt {cls : RegClass} {r : Reg} {off : Nat} {i : MInst}
    (h : i ∈ slotLoadAt cls r off) : MvShape i := by
  unfold slotLoadAt at h
  split at h
  · simp only [List.mem_singleton] at h; subst h
    cases cls <;> exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
  · rcases List.mem_append.1 h with h | h
    · exact mvShape_spAddrX16 h
    · simp only [List.mem_singleton] at h; subst h
      cases cls <;> exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))

/-- Move code consists of `MvShape` instructions. (Named `moveInsts_mvShape`: the name
`moveInsts_shape` is `RegLevelFwd`'s.) -/
theorem moveInsts_mvShape {fr : RAFrame} {src dst : Loc} {code : List AInst}
    (h : fr.moveInsts src dst = .ok code) :
    ∃ is : List MInst, code = is.map AInst.inst ∧ ∀ i ∈ is, MvShape i := by
  cases src with
  | reg a =>
    cases dst with
    | reg b =>
      simp only [RAFrame.moveInsts] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨[_], rfl, fun i hi => ?_⟩
        simp only [List.mem_singleton] at hi
        exact .inl ⟨_, _, _, hi⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨_, rfl, fun i hi => ?_⟩
        rcases List.mem_append.1 hi with hi | hi
        · exact mvShape_slotStoreAt hi
        · exact mvShape_slotLoadAt hi
    | save _ =>
      simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, by simp⟩
    | stack _ _ =>
      simp only [RAFrame.moveInsts, bind, Except.bind] at h
      split at h
      · cases h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨_, rfl, fun i hi => mvShape_slotStoreAt hi⟩
  | save _ =>
    cases dst <;>
    · simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, by simp⟩
  | stack _ _ =>
    cases dst with
    | reg b =>
      simp only [RAFrame.moveInsts, bind, Except.bind] at h
      split at h
      · cases h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨_, rfl, fun i hi => mvShape_slotLoadAt hi⟩
    | save _ =>
      simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, by simp⟩
    | stack _ _ => cases h

theorem kinds_mem_none {ls : List Line} (h : Concurrency.Code.kinds ls = []) {x : Insn}
    {t : Option Clif.TrapCode} (hx : Line.ins x t ∈ ls) : Concurrency.Code.insnKind x = none :=
  List.filterMap_eq_nil_iff.1 h _ hx

/-- No line of an `MvShape` instruction is an exclusive. -/
theorem mvShape_noExcl (ctx : FnCtx) {i : MInst} (hi : MvShape i) {ps ps' : PState}
    {ls : List Line} (hl : i.lines ctx ps = .ok (ls, ps')) :
    ∀ x t, Line.ins x t ∈ ls → ∀ env ai, x.toArmInst env = .ok ai → isExcl ai = false := by
  intro x t hx env ai ha
  have one : ∀ y, Concurrency.Code.insnKind y = none →
      ([Line.ins y] : List Line) = ls → isExcl ai = false := fun y hy e => by
    subst e
    simp only [List.mem_singleton, Line.ins.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact isExcl_none ha hy
  rcases hi with ⟨sz, rd, rm, rfl⟩ | ⟨op, r, m, fl, rfl⟩ | ⟨op, r, m, fl, rfl⟩ |
    ⟨op, rd, c, sz, rfl⟩ | ⟨rd, rn, c, sz, rfl⟩ | ⟨op, sz, rd, rn, rm, e, rfl⟩
  · simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    exact one _ (by split <;> rfl) hl.1
  · simp only [MInst.lines, bind, Except.bind] at hl
    split at hl
    · cases hl
    rename_i v hf
    obtain ⟨pre, m'⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rcases List.mem_append.1 hx with hx | hx
    · exact isExcl_none ha (kinds_mem_none (Concurrency.Code.kinds_memFinalize hf) hx)
    · simp only [List.mem_singleton, Line.ins.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      exact isExcl_store ha
  · simp only [MInst.lines, bind, Except.bind] at hl
    split at hl
    · cases hl
    rename_i v hf
    obtain ⟨pre, m'⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    rcases List.mem_append.1 hx with hx | hx
    · exact isExcl_none ha (kinds_mem_none (Concurrency.Code.kinds_memFinalize hf) hx)
    · simp only [List.mem_singleton, Line.ins.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      exact isExcl_load ha
  all_goals
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl
    exact one _ rfl hl.1

/-- The lines of instructions `is`: each line is a line of one of them. -/
theorem mem_codeLinesE (ctx : FnCtx) (af : AFunc) :
    ∀ (is : List MInst) {ps ps' : PState} {ls : List Line},
      codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps') →
      ∀ ln ∈ ls, ∃ i ∈ is, ∃ ps1 ls1 ps1', i.lines ctx ps1 = .ok (ls1, ps1') ∧ ln ∈ ls1
  | [], ps, ps', ls, h => by
    simp only [List.map_nil, codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro ln hln; cases hln
  | i :: is, ps, ps', ls, h => by
    simp only [List.map_cons, codeLinesE, ainstLines, bind, Except.bind] at h
    split at h
    · cases h
    rename_i v1 h1
    obtain ⟨l1, ps1⟩ := v1
    split at h
    · cases h
    rename_i v2 h2
    obtain ⟨l2, ps2⟩ := v2
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · exact ⟨i, by simp, ps, l1, ps1, h1, hln⟩
    · obtain ⟨j, hj, r⟩ := mem_codeLinesE ctx af is h2 ln hln
      exact ⟨j, by simp [hj], r⟩

-- `hchk` is not needed: every `moveInsts` output is `MvShape` code (`moveInsts_mvShape`).
set_option linter.unusedVariables false in
/-- **No line of a move is a store exclusive.** -/
theorem moveLines_noStx {vc : VCode} {rf : RFunc} (ctx : FnCtx) (af : AFunc) {c : CheckCtx}
    {wh : String} {src dst : Loc} (hchk : c.checkMove wh src dst = .ok ())
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {ls : List Line} {ps ps' : PState} (hls : codeLinesE ctx af code ps = .ok (ls, ps')) :
    ∀ x t, Line.ins x t ∈ ls → ∀ env ai, x.toArmInst env = .ok ai →
      ∀ rel rs rn, Concurrency.ArmInstFoot.clsOf ai ≠ .stx rel rs rn := by
  obtain ⟨is, rfl, hsh⟩ := moveInsts_mvShape hmi
  intro x t hx env ai ha rel rs rn
  obtain ⟨i, hi, ps1, ls1, ps1', hl1, hx1⟩ := mem_codeLinesE ctx af is hls _ hx
  exact clsOf_ne_stx (mvShape_noExcl ctx (hsh i hi) hl1 x t hx1 env ai ha) rel rs rn

end Backend.Proof
