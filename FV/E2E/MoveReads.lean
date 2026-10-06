import FV.E2E.RegLevelMove
import FV.E2E.ExecReads

/-!
# The memory reads of move code (L3 (c), D2)

`moveInsts_reads`: the code of a checked move (`RAFrame.moveInsts`), run from `s`, reads only
bytes of the frame's slot area at `spOf s` (`SlotArea`): its slot loads read `[sp, #off]` or,
beyond 32 KiB, `[x16]` after `x16 = sp + off` (`spAddrX16`), at a live slot or the float-move
scratch slot (`slotLoadAt_reads`); its slot stores read nothing (`slotStoreAt_noLoads`).
`linesReads_of_insts` turns this into the reads of the move's lines.
-/

namespace Backend.Proof

open Backend E2E

/-- The reads of a list of allocated instructions run in sequence from `s` (`ExecAll`): each
instruction's lines, from the state the instructions before it reach, read only `P`. -/
def InstsReads (ctx : FnCtx) (is : List MInst) (s : Arm.ArmState) (P : BitVec 64 → Prop) : Prop :=
  ∀ k i t, is[k]? = some i → ExecAll ctx (is.take k) s t → ∀ ps ls ps',
    i.lines ctx ps = .ok (ls, ps') → ∀ env, LinesReads env ls t P

theorem ExecAll.det {ctx : FnCtx} :
    ∀ {is : List MInst} {s t t' : Arm.ArmState}, ExecAll ctx is s t → ExecAll ctx is s t' → t = t'
  | [], _, _, _, h, h' => by simp only [ExecAll] at h h'; rw [h, h']
  | _ :: _, _, _, _, ⟨u, hu, _, _, h⟩, ⟨u', hu', _, _, h'⟩ => by
    have := (hu env0).symm.trans (hu' env0)
    cases this
    exact ExecAll.det h h'

theorem ExecAll.split {ctx : FnCtx} :
    ∀ {A B : List MInst} {s t : Arm.ArmState}, ExecAll ctx (A ++ B) s t →
      ∃ m, ExecAll ctx A s m ∧ ExecAll ctx B m t
  | [], _, s, _, h => ⟨s, rfl, h⟩
  | _ :: _, _, _, _, ⟨u, hu, he, hp, h⟩ => by
    obtain ⟨m, h1, h2⟩ := ExecAll.split h
    exact ⟨m, ⟨u, hu, he, hp, h1⟩, h2⟩

theorem InstsReads.mono {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState} {P Q : BitVec 64 → Prop}
    (h : InstsReads ctx is s P) (hPQ : ∀ a, P a → Q a) : InstsReads ctx is s Q :=
  fun k i t hk ht ps ls ps' hl env => (h k i t hk ht ps ls ps' hl env).mono hPQ

/-- Instructions without `memRd` read nothing. -/
theorem instsReads_noLoads {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState}
    {P : BitVec 64 → Prop} (h : ∀ i ∈ is, i.memRd = false) : InstsReads ctx is s P :=
  fun _ i _ hk _ _ _ _ hl _ => linesReads_noLoads (lines_noLoads hl (h i (List.mem_of_getElem? hk)))

theorem instsReads_append {ctx : FnCtx} {A B : List MInst} {s s1 : Arm.ArmState}
    {P : BitVec 64 → Prop} (hA : InstsReads ctx A s P) (hex : ExecAll ctx A s s1)
    (hB : InstsReads ctx B s1 P) : InstsReads ctx (A ++ B) s P := by
  intro k i t hk ht ps ls ps' hl env
  rcases Nat.lt_or_ge k A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at ht
    exact hA k i t hk ht ps ls ps' hl env
  · rw [List.getElem?_append_right hge] at hk
    rw [List.take_append, List.take_of_length_le hge] at ht
    obtain ⟨m, h1, h2⟩ := ExecAll.split ht
    obtain rfl := ExecAll.det h1 hex
    exact hB _ i t hk h2 ps ls ps' hl env

/-- A single instruction. -/
theorem instsReads_single {ctx : FnCtx} {i : MInst} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ ps ls ps', i.lines ctx ps = .ok (ls, ps') → ∀ env, LinesReads env ls s P) :
    InstsReads ctx [i] s P := by
  intro k i' t hk ht ps ls ps' hl env
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [List.take_zero, ExecAll] at ht
    subst ht
    exact h ps ls ps' hl env
  | succ k => simp at hk

/-- **The lines of one-line instructions run in sequence** read what the instructions read. -/
theorem linesReads_of_insts (ctx : FnCtx) (af : AFunc) {P : BitVec 64 → Prop} :
    ∀ (is : List MInst) (s s' : Arm.ArmState), (∀ i ∈ is, OneLine ctx i) → ExecAll ctx is s s' →
      InstsReads ctx is s P → ∀ ls ps ps', codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps') →
      ∀ env, LinesReads env ls s P
  | [], s, s', _, _, _, ls, ps, ps', hc, env => by
    simp only [List.map_nil, codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    intro k x t hk; simp at hk
  | i :: is, s, s', hone, hex, hrd, ls, ps, ps', hc, env => by
    obtain ⟨t0, hex0, hte, htp, hrest⟩ := hex
    obtain ⟨x, t, hl, -, -⟩ := hone i (by simp)
    simp only [List.map_cons, codeLinesE, ainstLines, hl, bind, Except.bind] at hc
    split at hc
    · cases hc
    rename_i r hr
    obtain ⟨ls2, ps2⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.singleton_append] at hc
    obtain ⟨rfl, -⟩ := hc
    have h1 : ∀ env, execLines env [.ins x t] s = some t0 := fun env => by
      have := hex0 env
      simp only [execMInst, hl] at this
      exact this
    have hrd' : InstsReads ctx is t0 P := fun k j u hk hu ps ls ps' hl' env =>
      hrd (k + 1) j u (by simpa using hk) ⟨t0, hex0, hte, htp, by simpa using hu⟩ ps ls ps' hl' env
    have ih := linesReads_of_insts ctx af is t0 s' (fun j hj => hone j (by simp [hj])) hrest hrd'
      ls2 _ _ hr
    intro k y t' hk s1 hs1 env' a ha p hp q hq
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact hrd 0 i s rfl rfl ps _ ps (hl ps) env 0 _ _ rfl s1 hs1 env' a ha p hp q hq
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.take_succ_cons] at hs1
      rw [execLines_cons_of (h1 env)] at hs1
      exact ih _ k y t' hk s1 hs1 env' a ha p hp q hq

/-- The bytes a slot load of class `cls` reads. -/
def slotLoadBytes : RegClass → Nat
  | .int => 8
  | .float => 16

/-- **The reads of a slot load** `slotLoadAt cls r off` from `s`: the slot's bytes at
`sp + off`. -/
theorem slotLoadAt_reads (ctx : FnCtx) (cls : RegClass) (r : Reg) {off : Nat}
    (h16 : cls = .float → off % 16 = 0) (s : Arm.ArmState) :
    InstsReads ctx (slotLoadAt cls r off) s (fun a => ∃ k < slotLoadBytes cls,
      a = spOf s + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  unfold slotLoadAt
  split
  · rename_i hlt
    refine instsReads_single fun ps ls ps' hl env => ?_
    cases cls
    · refine (mload_reads ctx (m := .spOffset off) trivial (fun e => by cases e) hl env s).mono ?_
      rintro a ⟨k, hk, rfl⟩
      exact ⟨k, hk, by simp [AMode.addr]⟩
    · have h16' := h16 rfl
      refine (mload_reads ctx (m := .spOffset off) trivial ?_ hl env s).mono ?_
      · intro _ pre m' hf
        simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
        by_cases h9 : (off : Int) ≤ 255
        · rw [show simm9? (off : Int) = some off by simp [simm9?]; omega] at hf
          simp at hf
          exact .inr ⟨_, _, hf.2.symm⟩
        · rw [show simm9? (off : Int) = none by simp [simm9?]; omega,
            show uimm12Scaled? (off : Int) LoadOp.fpuLoad128.bytes = some off by
              simp [uimm12Scaled?, LoadOp.bytes]; omega] at hf
          simp at hf
          exact .inl ⟨_, _, hf.2.symm⟩
      · rintro a ⟨k, hk, rfl⟩
        exact ⟨k, hk, by simp [AMode.addr]⟩
  · obtain ⟨P, hx⟩ := execAll_spAddrX16 ctx off s
    refine instsReads_append (instsReads_noLoads ?_) hx
      (instsReads_single fun ps ls ps' hl env => ?_)
    · intro i hi
      simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false] at hi
      rcases hi with (rfl | ⟨p, -, rfl⟩) | rfl <;> rfl
    · have hfin : ∀ b, 0 < b → FinalAM b (.unsignedOffset (.x 16) 0) := fun b hb =>
        ⟨by simp [BaseOk], by simp, by simp⟩
      cases cls <;>
      · refine (mload_reads ctx (m := .unsignedOffset (.x 16) 0) (hfin _ (load_bytes_pos _))
          (fun _ pre m' hf => ?_) hl env _).mono ?_
        · rw [memFinalize_final ctx _ (hfin _ (load_bytes_pos _)), Except.ok.injEq,
            Prod.mk.injEq] at hf
          exact .inl ⟨_, _, hf.2.symm⟩
        · rintro a ⟨k, hk, rfl⟩
          refine ⟨k, hk, ?_⟩
          simp [AMode.addr, regX, pcx, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

/-- The 128-bit slot store at `[sp, #off]` is at an immediate offset. -/
theorem memFinalize_sp16 (ctx : FnCtx) {off : Nat} (h16 : off % 16 = 0) (hoff : off < 32768)
    {pre : List Line} {m' : AMode}
    (hf : memFinalize ctx (.spOffset off) StoreOp.fpuStore128.bytes = .ok (pre, m')) :
    pre = [] ∧ ((∃ k, m' = .unscaled .sp k) ∨ ∃ k, m' = .unsignedOffset .sp k) := by
  simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
  by_cases h9 : (off : Int) ≤ 255
  · rw [show simm9? (off : Int) = some off by simp [simm9?]; omega] at hf
    simp at hf
    exact ⟨hf.1, .inl ⟨_, hf.2.symm⟩⟩
  · rw [show simm9? (off : Int) = none by simp [simm9?]; omega,
      show uimm12Scaled? (off : Int) StoreOp.fpuStore128.bytes = some off by
        simp [uimm12Scaled?, StoreOp.bytes]; omega] at hf
    simp at hf
    exact ⟨hf.1, .inr ⟨_, hf.2.symm⟩⟩

/-- **The lines of a slot store hold no load** (the 128-bit store, which the model's
register-offset class reads, is at an immediate offset or at `[x16]`). -/
theorem slotStoreAt_noLoads (ctx : FnCtx) {cls : RegClass} {r : Reg} {off : Nat}
    (h16 : cls = .float → off % 16 = 0) {i : MInst} (hi : i ∈ slotStoreAt cls r off)
    {ps ps' : PState} {ls : List Line} (hl : i.lines ctx ps = .ok (ls, ps')) :
    ∀ x t, Line.ins x t ∈ ls → x.loads = false := by
  unfold slotStoreAt at hi
  split at hi
  · rename_i hlt
    simp only [List.mem_singleton] at hi
    subst hi
    cases cls
    · exact lines_noLoads hl rfl
    · simp only [slotStore, MInst.lines, bind, Except.bind] at hl
      split at hl
      · cases hl
      rename_i v hf
      obtain ⟨pre, m'⟩ := v
      obtain ⟨rfl, hm⟩ := memFinalize_sp16 ctx (h16 rfl) hlt hf
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.nil_append] at hl
      obtain ⟨rfl, -⟩ := hl
      intro x t hx
      simp only [List.mem_singleton, Line.ins.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      rcases hm with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rfl
  · rcases List.mem_append.1 hi with hi | hi
    · refine lines_noLoads hl ?_
      simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false] at hi
      rcases hi with (rfl | ⟨p, -, rfl⟩) | rfl <;> rfl
    · simp only [List.mem_singleton] at hi
      subst hi
      have hfin : ∀ b, FinalAM b (.unsignedOffset (.x 16) 0) := fun b =>
        ⟨by simp [BaseOk], by simp, by simp⟩
      cases cls <;>
      · simp only [MInst.lines, memFinalize_final ctx _ (hfin _), bind, Except.bind, pure,
          Except.pure, Except.ok.injEq, Prod.mk.injEq, List.nil_append] at hl
        obtain ⟨rfl, -⟩ := hl
        intro x t hx
        simp only [List.mem_singleton, Line.ins.injEq] at hx
        obtain ⟨rfl, -⟩ := hx
        rfl

theorem instsReads_slotStoreAt (ctx : FnCtx) {cls : RegClass} {r : Reg} {off : Nat}
    (h16 : cls = .float → off % 16 = 0) (s : Arm.ArmState) (P : BitVec 64 → Prop) :
    InstsReads ctx (slotStoreAt cls r off) s P :=
  fun _ _ _ hk _ _ _ _ hl _ =>
    linesReads_noLoads (slotStoreAt_noLoads ctx h16 (List.mem_of_getElem? hk) hl)

/-- The slot area of a frame of `size` bytes at `sp`. -/
def SlotArea (size : Nat) (sp a : BitVec 64) : Prop :=
  ∃ o < size, a = sp + BitVec.ofNat 64 o

theorem slotLoadAt_area (ctx : FnCtx) (cls : RegClass) (r : Reg) {off size : Nat}
    (h16 : cls = .float → off % 16 = 0) (hle : off + slotLoadBytes cls ≤ size) (s : Arm.ArmState) :
    InstsReads ctx (slotLoadAt cls r off) s (SlotArea size (spOf s)) :=
  (slotLoadAt_reads ctx cls r h16 s).mono fun _ ⟨k, hk, e⟩ =>
    ⟨off + k, by omega, by rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]⟩

/-- **The reads of move code** (`RAFrame.moveInsts` of a checked move between live locations),
run from `s`: bytes of the frame's slot area at `spOf s`. -/
theorem moveInsts_reads {vc : VCode} {rf : RFunc} (ctx : FnCtx) {c : CheckCtx} {wh : String}
    {src dst : Loc} (hchk : c.checkMove wh src dst = .ok ()) (hLs : Live rf src)
    (hLd : Live rf dst) (hT : ∀ a b, src = .reg (.v a) → dst = .reg (.v b) → rf.floatMove = true)
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ is, code = is.map AInst.inst ∧
      InstsReads ctx is s (SlotArea (RAFrame.compute vc rf).size (spOf s)) := by
  obtain ⟨cls, hcls, hs, hd, hreg⟩ := checkMove_facts hchk
  have hdcls := locOk_cls hd
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
        exact ⟨[.mov .size64 (.x b') (.x a')], rfl, instsReads_noLoads fun i hi => by
          simp only [List.mem_singleton] at hi; subst hi; rfl⟩
      | float =>
        obtain ⟨a', rfl⟩ := reg_float hac
        obtain ⟨b', rfl⟩ := reg_float hbc
        simp only [RAFrame.moveInsts, hac, pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        have hfm := hT a' b' rfl rfl
        rcases allocatable_cases haa with ⟨_, e, _⟩ | ⟨_, e, ha⟩ <;> cases e
        have htmp := (compute_facts vc rf).2.2.2 hfm
        have hal := (compute_align vc rf).2.2
        obtain ⟨P, X, hx1⟩ := exec_slotStoreAt_float ctx ha hal halign
        refine ⟨_, rfl, instsReads_append (instsReads_slotStoreAt ctx (fun _ => hal) s _) hx1 ?_⟩
        have hsp : spOf (stSt (pcx s 16 P X) (RAFrame.compute vc rf).fmoveTmp 16
            (Arm.r (.SFP (rnum a')) (pcx s 16 P X))) = spOf s := by
          simp only [stSt, spOf_write, pcx_sp]
        rw [← hsp]
        exact slotLoadAt_area ctx .float _ (fun _ => hal) htmp _
    | stack k cl | save r =>
      all_goals
        simp only [RAFrame.moveInsts, bind, Except.bind] at hmi
        split at hmi
        · cases hmi
        rename_i o hoff
        simp only [pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        simp only [hac, Option.getD_some]
        refine ⟨_, rfl, instsReads_slotStoreAt ctx (fun e => ?_) s _⟩
        subst e
        have hal := live_align hLd hoff
        rw [slotBytes_float (fun _ h => by cases h) hdcls] at hal
        exact hal.1
  | stack k cl | save r =>
    all_goals
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
        refine ⟨_, rfl, ?_⟩
        have hal := live_align hLs hoff
        simp only [hbc, Option.getD_some]
        cases cls with
        | int =>
          rw [slotBytes_int (fun _ h => by cases h) hcls] at hal
          exact slotLoadAt_area ctx .int _ nofun hal.2 s
        | float =>
          rw [slotBytes_float (fun _ h => by cases h) hcls] at hal
          exact slotLoadAt_area ctx .float _ (fun _ => hal.1) hal.2 s

end Backend.Proof
