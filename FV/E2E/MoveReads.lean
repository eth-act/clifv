import FV.E2E.RegLevelMove
import FV.E2E.ExecReads

/-!
# The memory reads of move code (L3 (c), D2)

`moveInsts_reads`: the lines of a checked move (`RAFrame.moveInsts`), run from a state at the
frame's `sp`, read only the bytes of the slots of its locations (and of the float-move scratch
slot): a slot load `[sp, #off]` or, beyond 32 KiB, `[x16]` after `x16 = sp + off`
(`spAddrX16`). With the frame laid out in the slot area (`FrameOk`), these bytes lie in the
activation's frame.
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

/-- The loads of move code (spill reloads): `[sp, #off]` (`ldur`/`ldr`) and `[x16]`. -/
def _root_.Backend.Insn.slotLoad : Insn → Bool
  | .load _ _ (.unscaled .sp _) | .load _ _ (.unsignedOffset .sp _)
  | .load _ _ (.unsignedOffset (.x 16) 0) => true
  | _ => false

/-- A line of one-line instructions' code is the line of one of them. -/
theorem moveLines_mem {ctx : FnCtx} {af : AFunc} {x : Insn} {t : Option Clif.TrapCode} :
    ∀ {is : List MInst} {ps ps' : PState} {ls : List Line}, (∀ i ∈ is, OneLine ctx i) →
      codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps') → Line.ins x t ∈ ls →
      ∃ i ∈ is, ∃ ps0, i.lines ctx ps0 = .ok ([.ins x t], ps0)
  | [], _, _, _, _, hc, hx => by
    simp only [List.map_nil, codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    simp at hx
  | i :: is, ps, ps', ls, hone, hc, hx => by
    obtain ⟨y, u, hl, -, -⟩ := hone i (by simp)
    simp only [List.map_cons, codeLinesE, ainstLines, hl, bind, Except.bind] at hc
    split at hc
    · cases hc
    rename_i r hr
    obtain ⟨ls2, ps2⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.singleton_append] at hc
    obtain ⟨rfl, -⟩ := hc
    rcases List.mem_cons.1 hx with h | h
    · simp only [Line.ins.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨i, by simp, ps, hl ps⟩
    · obtain ⟨j, hj, ps0, h0⟩ := moveLines_mem (fun j hj => hone j (by simp [hj])) hr h
      exact ⟨j, by simp [hj], ps0, h0⟩

/-- **The loads of move code** are slot loads. -/
theorem moveInst_slotLoad (ctx : FnCtx) {i : MInst} (h : MoveInst i) {ps : PState} {x : Insn}
    {t : Option Clif.TrapCode} (hl : i.lines ctx ps = .ok ([.ins x t], ps)) (hx : x.loads = true) :
    x.slotLoad = true := by
  rcases h with ⟨a, b, rfl⟩ | ⟨cls, r, off, h8, h16, hoff, rfl | rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | rfl |
    ⟨op, r, rfl⟩ | ⟨op, r, rfl⟩
  all_goals (try (cases cls))
  all_goals simp [MInst.lines, slotLoad, slotStore, memFinalize, pure, Except.pure,
    bind, Except.bind] at hl
  all_goals (repeat' split at hl)
  all_goals first
    | (obtain ⟨rfl, -⟩ := hl; simp_all [Insn.loads, Insn.slotLoad]; done)
    | (simp_all [Insn.loads, Insn.slotLoad]; done)
    | (have hu := ‹uimm12Scaled? _ _ = none›
       simp [uimm12Scaled?, StoreOp.bytes, LoadOp.bytes] at hu
       (try have := h16 rfl)
       omega)

end Backend.Proof
