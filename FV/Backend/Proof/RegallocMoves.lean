import FV.Backend.Proof.RegallocSlots

/-!
# Lowering of every checked move (M6 proof)

`lower_move`: for a move the checker accepts (`checkMove`) between live locations, the code
`RAFrame.moveInsts` produces runs (`ExecAll`) and changes the location store exactly as
`MStep.move` does (`upd m dst (m src)`), keeping the world, `sp` and its alignment. Cases:
int register moves (`mov`), int spills/reloads and save/restore of x registers (8-byte slots),
float spills/reloads and save/restore of v registers (16-byte slots), float register moves
through `fmoveTmp` (a store and a load).
-/

namespace Backend.Proof
open Backend

/-- Run a list of instructions in sequence (at any code position: frame moves do not read
the pc). -/
def ExecAll (ctx : FnCtx) : List MInst → Arm.ArmState → Arm.ArmState → Prop
  | [], s, s' => s' = s
  | i :: is, s, s' => ∃ t, (∀ env, execMInst ctx env i s = some t) ∧
      Arm.r .ERR t = Arm.r .ERR s ∧ t.program = s.program ∧ ExecAll ctx is t s'

/-- The state facts a move keeps. -/
structure MoveOk (fr : RAFrame) (L : Loc → Prop) (F : BitVec 64 → Prop) (sp0 : BitVec 64)
    (s s' w : Arm.ArmState) (dst : Loc) (v : CV) : Prop where
  world : SameWorld F s' w
  sp : spOf s' = sp0
  store : ∀ l, ValidLoc l → L l → locVal fr s' l = upd (locVal fr s) dst v l
  /-- memory outside the frame's slot area `[sp0, sp0 + size)` is unchanged -/
  mem : ∀ a, (∀ o, o < fr.size → a ≠ sp0 + BitVec.ofNat 64 o) → s'.mem a = s.mem a

theorem stSt_err (s : Arm.ArmState) (o n : Nat) (v : BitVec (n * 8)) :
    Arm.r .ERR (stSt s o n v) = Arm.r .ERR s := by
  rw [stSt, Arm.r_of_w_different (by simp), Arm.r_of_write_mem_bytes]

theorem stSt_prog (s : Arm.ArmState) (o n : Nat) (v : BitVec (n * 8)) :
    (stSt s o n v).program = s.program := by
  rw [stSt, Arm.w_program, Arm.write_mem_bytes_program]

theorem stSt_mem {s : Arm.ArmState} {o n : Nat} {v : BitVec (n * 8)} {a : BitVec 64}
    (h : ∀ k < n, a ≠ spOf s + BitVec.ofNat 64 o + BitVec.ofNat 64 k) :
    (stSt s o n v).mem a = s.mem a := by
  rw [stSt, Arm.ArmState.mem_w_eq_mem, Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
  exact write_bytes_outside n _ v _ h

theorem ldIntSt_err (s : Arm.ArmState) (o n : Nat) : Arm.r .ERR (ldIntSt s o n) = Arm.r .ERR s := by
  rw [ldIntSt, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
theorem ldIntSt_prog (s : Arm.ArmState) (o n : Nat) : (ldIntSt s o n).program = s.program := by
  rw [ldIntSt, Arm.w_program, Arm.w_program]
theorem ldIntSt_mem (s : Arm.ArmState) (o n : Nat) : (ldIntSt s o n).mem = s.mem := by
  rw [ldIntSt, Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]
theorem ldFSt_err (s : Arm.ArmState) (o n : Nat) : Arm.r .ERR (ldFSt s o n) = Arm.r .ERR s := by
  rw [ldFSt, Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
theorem ldFSt_prog (s : Arm.ArmState) (o n : Nat) : (ldFSt s o n).program = s.program := by
  rw [ldFSt, Arm.w_program, Arm.w_program]
theorem ldFSt_mem (s : Arm.ArmState) (o n : Nat) : (ldFSt s o n).mem = s.mem := by
  rw [ldFSt, Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]

theorem ne_slot_addr {sp0 a : BitVec 64} {size o n : Nat} (hsz : size < 32768) (hle : o + n ≤ size)
    (h : ∀ o', o' < size → a ≠ sp0 + BitVec.ofNat 64 o') :
    ∀ k < n, a ≠ sp0 + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  intro k hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem align_of_sp {s t : Arm.ArmState} (h : spOf t = spOf s) (ha : Arm.CheckSPAlignment s) :
    Arm.CheckSPAlignment t := by
  simp only [Arm.CheckSPAlignment, Arm.read_gpr] at ha ⊢
  simpa only [spOf] using (show Arm.r (.GPR 31#5) t = Arm.r (.GPR 31#5) s from h) ▸ ha

section
variable {vc : VCode} {rf : RFunc} {T : Prop} {sp0 : BitVec 64} {F : BitVec 64 → Prop}

local notation "FR" => RAFrame.compute vc rf

theorem move_store_int (hfr : FrameOk FR (Live rf) T sp0 F) (hsz : (FR).size < 32768)
    (ctx : FnCtx) {a : Nat} (ha : (Reg.x a).allocatable = true) {dst : Loc} {o : Nat}
    (hD : Live rf dst) (hoff : (FR).offset dst = .ok o) (h8 : slotBytes dst = 8)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    ∃ s', ExecAll ctx [slotStore .int (.x a) o] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w dst (locVal FR s (.reg (.x a))) := by
  rcases allocatable_cases ha with ⟨a', ea, hha⟩ | ⟨_, ea, _⟩ <;> cases ea
  obtain ⟨hal, hle⟩ := live_align hD hoff
  rw [h8] at hal hle
  refine ⟨_, ⟨_, fun env => exec_store_int ctx env hha.1 hal (by omega) halign,
    stSt_err _ _ _ _, stSt_prog _ _ _ _, rfl⟩, ?_⟩
  obtain ⟨hW, hS, hO⟩ := store_effect hfr hw hsp hD hoff h8 (Arm.r (.GPR (rnum a)) s)
  refine ⟨hW, hS, fun l _ hl => ?_, fun a' ha' => stSt_mem (by rw [hsp]; exact ne_slot_addr hsz hle ha')⟩
  by_cases e : l = dst
  · subst e; simp only [upd, if_true]; rw [store_dst8 hoff h8]; rfl
  · simp only [upd, e, if_false]; exact hO l hl e

theorem move_store_float (hfr : FrameOk FR (Live rf) T sp0 F) (hsz : (FR).size < 32768)
    (ctx : FnCtx) {a : Nat} (ha : a < 32) {dst : Loc} {o : Nat}
    (hD : Live rf dst) (hoff : (FR).offset dst = .ok o) (h16 : slotBytes dst = 16)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    ∃ s', ExecAll ctx [slotStore .float (.v a) o] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w dst (locVal FR s (.reg (.v a))) := by
  obtain ⟨hal, hle⟩ := live_align hD hoff
  rw [h16] at hal hle
  refine ⟨_, ⟨_, fun env => exec_store_float ctx env ha hal (by omega) halign,
    stSt_err _ _ _ _, stSt_prog _ _ _ _, rfl⟩, ?_⟩
  obtain ⟨hW, hS, hO⟩ := store_effect hfr hw hsp hD hoff h16 (Arm.r (.SFP (rnum a)) s)
  refine ⟨hW, hS, fun l _ hl => ?_, fun a' ha' => stSt_mem (by rw [hsp]; exact ne_slot_addr hsz hle ha')⟩
  by_cases e : l = dst
  · subst e; simp only [upd, if_true]; rw [store_dst16 hoff h16]; rfl
  · simp only [upd, e, if_false]; exact hO l hl e

theorem move_load_int (hsz : (FR).size < 32768) (ctx : FnCtx) {b : Nat}
    (hb : (Reg.x b).allocatable = true) {src : Loc} {o : Nat}
    (hD : Live rf src) (hoff : (FR).offset src = .ok o) (h8 : slotBytes src = 8)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    ∃ s', ExecAll ctx [slotLoad .int (.x b) o] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w (.reg (.x b)) (locVal FR s src) := by
  rcases allocatable_cases hb with ⟨b', eb, hhb⟩ | ⟨_, eb, _⟩ <;> cases eb
  obtain ⟨hal, hle⟩ := live_align hD hoff
  rw [h8] at hal hle
  refine ⟨_, ⟨_, fun env => exec_load_int ctx env hhb.1 hal (by omega) halign,
    ldIntSt_err _ _ _, ldIntSt_prog _ _ _, rfl⟩, ?_⟩
  obtain ⟨hW, hS, hO⟩ := loadInt_effect (fr := FR) hw hb hoff h8
  exact ⟨hW, hS.trans hsp, fun l hl _ => hO l hl, fun a _ => by rw [ldIntSt_mem]⟩

theorem move_load_float (hsz : (FR).size < 32768) (ctx : FnCtx) {b : Nat} (hb : b < 32)
    {src : Loc} {o : Nat} (hD : Live rf src) (hoff : (FR).offset src = .ok o)
    (h16 : slotBytes src = 16) {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    ∃ s', ExecAll ctx [slotLoad .float (.v b) o] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w (.reg (.v b)) (locVal FR s src) := by
  obtain ⟨hal, hle⟩ := live_align hD hoff
  rw [h16] at hal hle
  refine ⟨_, ⟨_, fun env => exec_load_float ctx env hb hal (by omega) halign,
    ldFSt_err _ _ _, ldFSt_prog _ _ _, rfl⟩, ?_⟩
  obtain ⟨hW, hS, hO⟩ := loadFloat_effect (fr := FR) hw hb hoff h16
  exact ⟨hW, hS.trans hsp, fun l hl _ => hO l hl, fun a _ => by rw [ldFSt_mem]⟩

theorem move_reg_int (ctx : FnCtx) {a b : Nat} (ha : (Reg.x a).allocatable = true)
    (hb : (Reg.x b).allocatable = true) {s w : Arm.ArmState} (hw : SameWorld F s w)
    (hsp : spOf s = sp0) :
    ∃ s', ExecAll ctx [.mov .size64 (.x b) (.x a)] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w (.reg (.x b)) (locVal FR s (.reg (.x a))) := by
  obtain ⟨-, s', hex, hW, hS, hO⟩ := lower_move_reg_int FR F ctx (⟨0, fun _ => none⟩ : Env) ha hb hw
  rcases allocatable_cases ha with ⟨a', ea, hha⟩ | ⟨_, ea, _⟩ <;> cases ea
  rcases allocatable_cases hb with ⟨b', eb, hhb⟩ | ⟨_, eb, _⟩ <;> cases eb
  have hex' : ∀ env, execMInst ctx env (.mov .size64 (.x b) (.x a)) s = some s' := fun env => by
    rw [exec_mov64 ctx env hhb.1 hha.1 s]; rw [exec_mov64 ctx (⟨0, fun _ => none⟩ : Env) hhb.1 hha.1 s] at hex; exact hex
  have hs' : s' = Arm.w (.GPR (rnum b)) (Arm.r (.GPR (rnum a)) s) (Arm.w .PC (Arm.r .PC s + 4#64) s) := by
    have := hex' (⟨0, fun _ => none⟩ : Env)
    rw [exec_mov64 ctx _ hhb.1 hha.1 s] at this
    exact (Option.some.inj this).symm
  exact ⟨s', ⟨s', hex', by rw [hs', Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)],
    by rw [hs', Arm.w_program, Arm.w_program], rfl⟩, hW, hS.trans hsp, fun l hl _ => hO l hl,
    fun a _ => by rw [hs', Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]⟩

/-- A float register move: store to `fmoveTmp`, load from it. -/
theorem move_reg_float (hfr : FrameOk FR (Live rf) T sp0 F) (hT : T) (hsz : (FR).size < 32768)
    (ctx : FnCtx) {a b : Nat} (ha : a < 32) (hb : b < 32) {s w : Arm.ArmState}
    (hw : SameWorld F s w) (hsp : spOf s = sp0) (halign : Arm.CheckSPAlignment s)
    (htmp : (FR).fmoveTmp + 16 ≤ (FR).size) :
    ∃ s', ExecAll ctx [slotStore .float (.v a) (FR).fmoveTmp, slotLoad .float (.v b) (FR).fmoveTmp] s s' ∧
      MoveOk FR (Live rf) F sp0 s s' w (.reg (.v b)) (locVal FR s (.reg (.v a))) := by
  have hal : (FR).fmoveTmp % 16 = 0 := (compute_align vc rf).2.2
  let t := stSt s (FR).fmoveTmp 16 (Arm.r (.SFP (rnum a)) s)
  have htsp : spOf t = sp0 := by simp only [t, stSt, spOf_write, hsp]
  have htw : SameWorld F t w := SameWorld.w_left (by simp [Masked])
    (SameWorld.write_mem_bytes_inF hw _ _ _ (fun j hj => by rw [hsp]; exact hfr.tmpF hT j hj))
  have htal : Arm.CheckSPAlignment t := align_of_sp (by simp only [t, stSt, spOf_write]) halign
  refine ⟨ldFSt t (FR).fmoveTmp b,
    ⟨t, fun env => exec_store_float ctx env ha hal (by omega) halign, stSt_err _ _ _ _,
      stSt_prog _ _ _ _,
      ⟨_, fun env => exec_load_float ctx env hb hal (by omega) htal, ldFSt_err _ _ _,
        ldFSt_prog _ _ _, rfl⟩⟩, ?_⟩
  -- the load reads what the store wrote
  have hrd : Arm.read_mem_bytes 16 (spOf t + BitVec.ofNat 64 (FR).fmoveTmp) t = Arm.r (.SFP (rnum a)) s := by
    simp only [t, stSt, spOf_write]
    rw [Arm.read_mem_bytes_of_w, Arm.read_mem_bytes_of_write_mem_bytes_same (by decide)]
  -- the store keeps every live location
  have hkeep : ∀ l, ValidLoc l → Live rf l → locVal FR t l = locVal FR s l := by
    intro l hl hL
    cases l with
    | reg r =>
      simp only [locVal, t, stSt]
      rw [regVal_w (by cases r <;> simp [Reg.field]), regVal_write_mem_bytes]
    | stack k c =>
      exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o ho => by
        rw [hsp]; exact hfr.tmpSep hT _ o hL ho)
    | save r =>
      exact locVal_frame_write (fun r h => Loc.noConfusion h) (fun o ho => by
        rw [hsp]; exact hfr.tmpSep hT _ o hL ho)
  refine ⟨SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) htw), ?_,
    fun l hl hL => ?_, fun a' ha' => ?_⟩
  · simp only [spOf, ldFSt]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    exact htsp
  · by_cases e : l = .reg (.v b)
    · subst e
      simp only [upd, if_true, locVal, ldFSt, regVal, Arm.r_of_w_same]
      rw [hrd]
    · simp only [upd, e, if_false]
      rw [← hkeep l hl hL]
      cases l with
      | reg r =>
        simp only [locVal, ldFSt]
        rw [regVal_w, regVal_w (by cases r <;> simp [Reg.field])]
        rcases allocatable_cases (hl r rfl) with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
        · simp [Reg.field]
        · simp only [Reg.field, ne_eq, Option.some.injEq, Arm.StateField.SFP.injEq]
          exact rnum_ne hk hb (fun h => e (by rw [h]))
      | stack k c =>
        exact locVal_frame_congr (fun r h => Loc.noConfusion h)
          (by simp only [spOf, ldFSt]; rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)])
          (by simp only [ldFSt]; rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem])
      | save r =>
        exact locVal_frame_congr (fun r h => Loc.noConfusion h)
          (by simp only [spOf, ldFSt]; rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)])
          (by simp only [ldFSt]; rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem])
  · rw [ldFSt_mem]
    exact stSt_mem (by rw [hsp]; exact ne_slot_addr hsz htmp ha')

end


theorem checkMove_facts {c : CheckCtx} {wh : String} {src dst : Loc}
    (h : c.checkMove wh src dst = .ok ()) :
    ∃ cls, src.cls? = some cls ∧ c.locOk src cls = true ∧ c.locOk dst cls = true ∧
      (src.isReg || dst.isReg) = true := by
  unfold CheckCtx.checkMove at h
  split at h
  · cases h
  · rename_i cls hcls
    obtain ⟨h1, h⟩ := Except.seq_ok h
    obtain ⟨h2, -⟩ := Except.seq_ok h
    have h1 := ensure_ok h1
    simp only [Bool.and_eq_true] at h1
    exact ⟨cls, hcls, h1.1, h1.2, ensure_ok h2⟩

theorem locOk_cls {c : CheckCtx} {l : Loc} {cls : RegClass} (h : c.locOk l cls = true) :
    l.cls? = some cls := by
  unfold CheckCtx.locOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem locOk_reg {c : CheckCtx} {r : Reg} {cls : RegClass} (h : c.locOk (.reg r) cls = true) :
    r.realClass? = some cls ∧ r.allocatable = true := by
  unfold CheckCtx.locOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

theorem slotBytes_int {l : Loc} (hl : ∀ r, l ≠ .reg r) (h : l.cls? = some .int) : slotBytes l = 8 := by
  cases l with
  | reg r => exact absurd rfl (hl r)
  | stack k c => simp only [Loc.cls?, Option.some.injEq] at h; subst h; rfl
  | save r => cases r <;> simp_all [Loc.cls?, Reg.realClass?, slotBytes]

theorem slotBytes_float {l : Loc} (hl : ∀ r, l ≠ .reg r) (h : l.cls? = some .float) : slotBytes l = 16 := by
  cases l with
  | reg r => exact absurd rfl (hl r)
  | stack k c => simp only [Loc.cls?, Option.some.injEq] at h; subst h; rfl
  | save r => cases r <;> simp_all [Loc.cls?, Reg.realClass?, slotBytes]

theorem reg_int {r : Reg} (h : r.realClass? = some .int) : ∃ n, r = .x n := by
  cases r <;> simp_all [Reg.realClass?]

theorem reg_float {r : Reg} (h : r.realClass? = some .float) : ∃ n, r = .v n := by
  cases r <;> simp_all [Reg.realClass?]

/-- The instructions move code consists of: `mov` between X registers, slot stores and loads
at an aligned offset of a frame below 32 KiB. -/
def MoveInst (i : MInst) : Prop :=
  (∃ a b, i = .mov .size64 (.x b) (.x a)) ∨
    ∃ cls r off, off % 8 = 0 ∧ (cls = .float → off % 16 = 0) ∧ off < 32768 ∧
      (i = slotStore cls r off ∨ i = slotLoad cls r off)

/-- **Lowering of a checked move.** -/
theorem lower_move {vc : VCode} {rf : RFunc} {sp0 : BitVec 64} {F : BitVec 64 → Prop}
    (hfr : FrameOk (RAFrame.compute vc rf) (Live rf) (rf.floatMove = true) sp0 F)
    (hsz : (RAFrame.compute vc rf).size < 32768) (ctx : FnCtx) {c : CheckCtx} {wh : String}
    {src dst : Loc} (hchk : c.checkMove wh src dst = .ok ()) (hLs : Live rf src) (hLd : Live rf dst)
    (hT : ∀ a b, src = .reg (.v a) → dst = .reg (.v b) → rf.floatMove = true)
    {code : List AInst} (hmi : (RAFrame.compute vc rf).moveInsts src dst = .ok code)
    {s w : Arm.ArmState} (hw : SameWorld F s w) (hsp : spOf s = sp0)
    (halign : Arm.CheckSPAlignment s) :
    ValidLoc src ∧ ValidLoc dst ∧ ∃ is s', code = is.map AInst.inst ∧ (∀ i ∈ is, MoveInst i) ∧
      ExecAll ctx is s s' ∧
      MoveOk (RAFrame.compute vc rf) (Live rf) F sp0 s s' w dst (locVal (RAFrame.compute vc rf) s src) := by
  obtain ⟨cls, hcls, hs, hd, hreg⟩ := checkMove_facts hchk
  have vloc : ∀ l, c.locOk l cls = true → ValidLoc l := fun l h r e => by
    subst e; exact (locOk_reg h).2
  refine ⟨vloc _ hs, vloc _ hd, ?_⟩
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
        obtain ⟨s', hx, hm⟩ := move_reg_int (vc := vc) (rf := rf) ctx haa hba hw hsp
        exact ⟨_, s', rfl, by simp [MoveInst], hx, hm⟩
      | float =>
        obtain ⟨a', rfl⟩ := reg_float hac
        obtain ⟨b', rfl⟩ := reg_float hbc
        simp only [RAFrame.moveInsts, hac, pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        have hfm := hT a' b' rfl rfl
        rcases allocatable_cases haa with ⟨_, e, _⟩ | ⟨_, e, ha⟩ <;> cases e
        rcases allocatable_cases hba with ⟨_, e, _⟩ | ⟨_, e, hb⟩ <;> cases e
        obtain ⟨s', hx, hm⟩ := move_reg_float hfr hfm hsz ctx ha hb hw hsp halign
          ((compute_facts vc rf).2.2.2 hfm)
        have htmp := (compute_facts vc rf).2.2.2 hfm
        have hal := (compute_align vc rf).2.2
        refine ⟨_, s', rfl, fun i hi => ?_, hx, hm⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact .inr ⟨.float, _, _, by omega, fun _ => hal, by omega, .inl rfl⟩
        · exact .inr ⟨.float, _, _, by omega, fun _ => hal, by omega, .inr rfl⟩
    | stack k cl | save r =>
      all_goals
        simp only [RAFrame.moveInsts, bind, Except.bind] at hmi
        split at hmi
        · cases hmi
        rename_i o hoff
        simp only [pure, Except.pure, Except.ok.injEq] at hmi
        subst hmi
        cases cls with
        | int =>
          obtain ⟨a', rfl⟩ := reg_int hac
          have hsb := slotBytes_int (fun _ h => by cases h) hdcls
          obtain ⟨s', hx, hm⟩ := move_store_int hfr hsz ctx haa hLd hoff hsb hw hsp halign
          have hal := live_align hLd hoff
          rw [hsb] at hal
          exact ⟨_, s', by simp [Reg.realClass?], fun i hi => .inr ⟨.int, _, _, hal.1, nofun, by omega,
            .inl (by simpa using hi)⟩, hx, hm⟩
        | float =>
          obtain ⟨a', rfl⟩ := reg_float hac
          rcases allocatable_cases haa with ⟨_, e, _⟩ | ⟨_, e, ha⟩ <;> cases e
          have hsb := slotBytes_float (fun _ h => by cases h) hdcls
          obtain ⟨s', hx, hm⟩ := move_store_float hfr hsz ctx ha hLd hoff hsb hw hsp halign
          have hal := live_align hLd hoff
          rw [hsb] at hal
          exact ⟨_, s', by simp [Reg.realClass?], fun i hi => .inr ⟨.float, _, _, by omega,
            fun _ => hal.1, by omega, .inl (by simpa using hi)⟩, hx, hm⟩
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
        cases cls with
        | int =>
          obtain ⟨b', rfl⟩ := reg_int hbc
          have hsb := slotBytes_int (fun _ h => by cases h) hcls
          obtain ⟨s', hx, hm⟩ := move_load_int hsz ctx hba hLs hoff hsb hw hsp halign
          have hal := live_align hLs hoff
          rw [hsb] at hal
          exact ⟨_, s', by simp [Reg.realClass?], fun i hi => .inr ⟨.int, _, _, hal.1, nofun, by omega,
            .inr (by simpa using hi)⟩, hx, hm⟩
        | float =>
          obtain ⟨b', rfl⟩ := reg_float hbc
          rcases allocatable_cases hba with ⟨_, e, _⟩ | ⟨_, e, hb⟩ <;> cases e
          have hsb := slotBytes_float (fun _ h => by cases h) hcls
          obtain ⟨s', hx, hm⟩ := move_load_float hsz ctx hb hLs hoff hsb hw hsp halign
          have hal := live_align hLs hoff
          rw [hsb] at hal
          exact ⟨_, s', by simp [Reg.realClass?], fun i hi => .inr ⟨.float, _, _, by omega,
            fun _ => hal.1, by omega, .inr (by simpa using hi)⟩, hx, hm⟩

end Backend.Proof
