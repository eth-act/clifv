import FV.E2E.MoveReads
import FV.E2E.ExecWrites

/-!
# The memory writes of move code (A3, #412, slice F8b)

`moveInsts_writes`: the code of a checked move (`RAFrame.moveInsts`), run from `s`, writes only
bytes of the frame's slot area at `spOf s` (`SlotArea`): its slot stores write `[sp, #off]` or,
beyond 32 KiB, `[x16]` after `x16 = sp + off` (`spAddrX16`), at a live slot or the float-move
scratch slot (`slotStoreAt_writes`); its slot loads write nothing. `linesWrites_of_insts` turns
this into the writes of the move's lines (as `moveInsts_reads`, `FV/E2E/MoveReads.lean`).
-/

namespace Backend.Proof

open Backend E2E

/-- The writes of a list of allocated instructions run in sequence from `s` (`ExecAll`): each
instruction's lines, from the state the instructions before it reach, write only `P`. -/
def InstsWrites (ctx : FnCtx) (is : List MInst) (s : Arm.ArmState) (P : BitVec 64 → Prop) : Prop :=
  ∀ k i t, is[k]? = some i → ExecAll ctx (is.take k) s t → ∀ ps ls ps',
    i.lines ctx ps = .ok (ls, ps') → ∀ env, LinesWrites env ls t P

theorem InstsWrites.mono {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState} {P Q : BitVec 64 → Prop}
    (h : InstsWrites ctx is s P) (hPQ : ∀ a, P a → Q a) : InstsWrites ctx is s Q :=
  fun k i t hk ht ps ls ps' hl env => (h k i t hk ht ps ls ps' hl env).mono hPQ

/-- Instructions without `memWr` write nothing. -/
theorem instsWrites_noStores {ctx : FnCtx} {is : List MInst} {s : Arm.ArmState}
    {P : BitVec 64 → Prop} (h : ∀ i ∈ is, i.memWr = false) : InstsWrites ctx is s P :=
  fun _ i _ hk _ _ _ _ hl _ => linesWrites_noStores (lines_noStores hl (h i (List.mem_of_getElem? hk)))

theorem instsWrites_append {ctx : FnCtx} {A B : List MInst} {s s1 : Arm.ArmState}
    {P : BitVec 64 → Prop} (hA : InstsWrites ctx A s P) (hex : ExecAll ctx A s s1)
    (hB : InstsWrites ctx B s1 P) : InstsWrites ctx (A ++ B) s P := by
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
theorem instsWrites_single {ctx : FnCtx} {i : MInst} {s : Arm.ArmState} {P : BitVec 64 → Prop}
    (h : ∀ ps ls ps', i.lines ctx ps = .ok (ls, ps') → ∀ env, LinesWrites env ls s P) :
    InstsWrites ctx [i] s P := by
  intro k i' t hk ht ps ls ps' hl env
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [List.take_zero, ExecAll] at ht
    subst ht
    exact h ps ls ps' hl env
  | succ k => simp at hk

/-- **The lines of one-line instructions run in sequence** write what the instructions write. -/
theorem linesWrites_of_insts (ctx : FnCtx) (af : AFunc) {P : BitVec 64 → Prop} :
    ∀ (is : List MInst) (s s' : Arm.ArmState), (∀ i ∈ is, OneLine ctx i) → ExecAll ctx is s s' →
      InstsWrites ctx is s P → ∀ ls ps ps', codeLinesE ctx af (is.map .inst) ps = .ok (ls, ps') →
      ∀ env, LinesWrites env ls s P
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
    have hrd' : InstsWrites ctx is t0 P := fun k j u hk hu ps ls ps' hl' env =>
      hrd (k + 1) j u (by simpa using hk) ⟨t0, hex0, hte, htp, by simpa using hu⟩ ps ls ps' hl' env
    have ih := linesWrites_of_insts ctx af is t0 s' (fun j hj => hone j (by simp [hj])) hrest hrd'
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

/-- **The writes of a slot store** `slotStoreAt cls r off` from `s`: the slot's bytes at
`sp + off`. -/
theorem slotStoreAt_writes (ctx : FnCtx) (cls : RegClass) (r : Reg) {off : Nat}
    (h16 : cls = .float → off % 16 = 0) (s : Arm.ArmState) :
    InstsWrites ctx (slotStoreAt cls r off) s (fun a => ∃ k < slotLoadBytes cls,
      a = spOf s + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  unfold slotStoreAt
  split
  · rename_i hlt
    refine instsWrites_single fun ps ls ps' hl env => ?_
    cases cls
    · refine (mstore_writes ctx (m := .spOffset off) trivial (fun e => by cases e) hl env s).mono ?_
      rintro a ⟨k, hk, rfl⟩
      exact ⟨k, hk, by simp [AMode.addr]⟩
    · have h16' := h16 rfl
      refine (mstore_writes ctx (m := .spOffset off) trivial ?_ hl env s).mono ?_
      · intro _ pre m' hf
        rcases (memFinalize_sp16 ctx h16' hlt hf).2 with ⟨k, e⟩ | ⟨k, e⟩
        · exact .inr ⟨_, _, e⟩
        · exact .inl ⟨_, _, e⟩
      · rintro a ⟨k, hk, rfl⟩
        exact ⟨k, hk, by simp [AMode.addr]⟩
  · obtain ⟨P, hx⟩ := execAll_spAddrX16 ctx off s
    refine instsWrites_append (instsWrites_noStores ?_) hx
      (instsWrites_single fun ps ls ps' hl env => ?_)
    · intro i hi
      simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false] at hi
      rcases hi with (rfl | ⟨p, -, rfl⟩) | rfl <;> rfl
    · have hfin : ∀ b, 0 < b → FinalAM b (.unsignedOffset (.x 16) 0) := fun b hb =>
        ⟨by simp [BaseOk], by simp, by simp⟩
      cases cls <;>
      · refine (mstore_writes ctx (m := .unsignedOffset (.x 16) 0) (hfin _ (store_bytes_pos _))
          (fun _ pre m' hf => ?_) hl env _).mono ?_
        · rw [memFinalize_final ctx _ (hfin _ (store_bytes_pos _)), Except.ok.injEq,
            Prod.mk.injEq] at hf
          exact .inl ⟨_, _, hf.2.symm⟩
        · rintro a ⟨k, hk, rfl⟩
          refine ⟨k, hk, ?_⟩
          simp [AMode.addr, regX, pcx, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

/-- A slot load writes nothing. -/
theorem instsWrites_slotLoadAt (ctx : FnCtx) (cls : RegClass) (r : Reg) (off : Nat)
    (s : Arm.ArmState) (P : BitVec 64 → Prop) : InstsWrites ctx (slotLoadAt cls r off) s P := by
  refine instsWrites_noStores fun i hi => ?_
  unfold slotLoadAt at hi
  split at hi
  · simp only [List.mem_singleton] at hi; subst hi; cases cls <;> rfl
  · rcases List.mem_append.1 hi with hi | hi
    · simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false] at hi
      rcases hi with (rfl | ⟨p, -, rfl⟩) | rfl <;> rfl
    · simp only [List.mem_singleton] at hi; subst hi; cases cls <;> rfl

theorem slotStoreAt_area (ctx : FnCtx) (cls : RegClass) (r : Reg) {off size : Nat}
    (h16 : cls = .float → off % 16 = 0) (hle : off + slotLoadBytes cls ≤ size) (s : Arm.ArmState) :
    InstsWrites ctx (slotStoreAt cls r off) s (SlotArea size (spOf s)) :=
  (slotStoreAt_writes ctx cls r h16 s).mono fun _ ⟨k, hk, e⟩ =>
    ⟨off + k, by omega, by rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]⟩

/-- **The writes of move code** (`RAFrame.moveInsts` of a checked move between live locations),
run from `s`: bytes of the frame's slot area at `spOf s`. -/
theorem moveInsts_writes {vc : VCode} {rf : RFunc} (ctx : FnCtx) {c : CheckCtx} {wh : String}
    {src dst : Loc} (hchk : c.checkMove wh src dst = .ok ()) (hLs : Live rf src)
    (hLd : Live rf dst) (hT : ∀ a b, src = .reg (.v a) → dst = .reg (.v b) → rf.floatMove = true)
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {s : Arm.ArmState} (halign : Arm.CheckSPAlignment s) :
    ∃ is, code = is.map AInst.inst ∧
      InstsWrites ctx is s (SlotArea (RAFrame.compute vc rf).size (spOf s)) := by
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
        exact ⟨[.mov .size64 (.x b') (.x a')], rfl, instsWrites_noStores fun i hi => by
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
        exact ⟨_, rfl, instsWrites_append (slotStoreAt_area ctx .float _ (fun _ => hal) htmp s) hx1
          (instsWrites_slotLoadAt ctx _ _ _ _ _)⟩
    | stack k cl | save r =>
      all_goals
        simp only [RAFrame.moveInsts, bind, Except.bind] at hmi
        split at hmi
        · cases hmi
        rename_i o hoff
        simp only [pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        simp only [hac, Option.getD_some]
        refine ⟨_, rfl, ?_⟩
        have hal := live_align hLd hoff
        cases cls with
        | int =>
          rw [slotBytes_int (fun _ h => by cases h) hdcls] at hal
          exact slotStoreAt_area ctx .int _ nofun hal.2 s
        | float =>
          rw [slotBytes_float (fun _ h => by cases h) hdcls] at hal
          exact slotStoreAt_area ctx .float _ (fun _ => hal.1) hal.2 s
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
        exact ⟨_, rfl, instsWrites_slotLoadAt ctx _ _ _ s _⟩

end Backend.Proof
