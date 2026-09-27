import FV.Compile.Proof.Arith

/-!
# The map model (`Compile.mapEnv`) on encoded maps

Specifications of the runtime externs in terms of the abstract heap `H`, the encoding of
keys/values as words (`toWord`), and preservation of the frame invariant `Ctx.Inv` across a
memory change that keeps the frame's own allocations.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame State Mem Program Function Block Inst Outcome Alloc evalInst)
open DSL (Ty IntW)

/-! ## Words -/

theorem toWord_inj {k : Ty} (hk : k.isKey = true) {a b : k.denote}
    (h : toWord k a = toWord k b) : a = b := by
  cases k with
  | int w =>
    simp only [toWord] at h
    apply BitVec.eq_of_toNat_eq
    have ha := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at ha
    have h1 : a.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le a.isLt
      (Nat.pow_le_pow_right (by decide) (by cases w <;> decide))
    have h2 : b.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le b.isLt
      (Nat.pow_le_pow_right (by decide) (by cases w <;> decide))
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ha
  | bool => cases a <;> cases b <;> simp_all [toWord]
  | _ => simp [DSL.Ty.isKey] at hk

theorem lookupL_enc {k v : Ty} (hk : k.isKey = true) (key : k.denote) :
    ∀ l : List (k.denote × v.denote),
      DSL.Map.lookupL (toWord k key) (l.map fun e => (toWord k e.1, toWord v e.2)) =
        (DSL.Map.lookupL key l).map (toWord v)
  | [] => rfl
  | (a, b) :: l => by
    simp only [List.map_cons, DSL.Map.lookupL]
    by_cases h : key = a
    · subst h; simp
    · have : toWord k key ≠ toWord k a := fun he => h (toWord_inj hk he)
      simp [h, this, lookupL_enc hk key l]

theorem upsertL_enc {k v : Ty} (hk : k.isKey = true) (key : k.denote) (x : v.denote) :
    ∀ l : List (k.denote × v.denote),
      DSL.Map.upsertL (toWord k key) (toWord v x) (l.map fun e => (toWord k e.1, toWord v e.2)) =
        (DSL.Map.upsertL key x l).map fun e => (toWord k e.1, toWord v e.2)
  | [] => rfl
  | (a, b) :: l => by
    simp only [List.map_cons, DSL.Map.upsertL]
    by_cases h : key = a
    · subst h; simp
    · have : toWord k key ≠ toWord k a := fun he => h (toWord_inj hk he)
      simp [h, this, upsertL_enc hk key x l]

theorem toWord_lt (k : Ty) (x : k.denote) : (toWord k x).toNat < 2 ^ 64 := (toWord k x).isLt

theorem ofNat_toWord (k : Ty) (x : k.denote) :
    BitVec.ofNat 64 (Val.ofNat .i64 (toWord k x).toNat).toNat = toWord k x := by
  simp [Val.ofNat, Val.toNat, Clif.Ty.width]

/-! ## The frame invariant across memory changes -/

theorem Ctx.Inv.mem_step {c : Ctx} {H H' : Heap} {s : State} (hI : c.Inv H s) {m' : Mem}
    (hm : MemModels m' H') (hg : Grows H H' s.mem.next)
    (hk : ∀ al ∈ s.mem.allocs, ObjFree H al.base → Keeps s.mem m' al) {fr' : Frame}
    (hf : fr'.func = s.frame.func) (hs : fr'.slots = s.frame.slots) {n : Nat}
    (ha : Agree s.frame.regs fr'.regs n) (hn : c.n0 ≤ n) :
    c.Inv H' { s with frame := fr', mem := m' } := by
  refine ⟨hf.trans hI.func, hs.trans hI.slots, hI.callers, hm, fun k ss hk' => ?_, fun b hb => ?_,
    hI.regs.agree ha hn⟩
  · obtain ⟨b, hl, hal, h16, hfree⟩ := hI.slotsOK k ss hk'
    have hlt := hI.mem.wf.below _ hal
    exact ⟨b, hl, (hk _ hal hfree hal).1, h16, hfree.grows hg (by simp at hlt; omega)⟩
  · obtain ⟨hal, hfree⟩ := hI.bufOK b hb
    have hlt := hI.mem.wf.below _ hal
    exact ⟨(hk _ hal hfree hal).1, hfree.grows hg (by simp at hlt; omega)⟩

/-! ## Extern specifications -/

variable {m : Mem} {H : Heap}

theorem spec_new (hm : MemModels m H) (ctx : Val) :
    ∃ f, mapEnv.extern "flat_map_new" = some f ∧
      (f [ctx] m = .trapped oomTrap ∨
       ∃ h m' d, f [ctx] m = .returned [Val.ofNat .i64 h] m' ∧ m.next ≤ h ∧ h < 2 ^ 64 ∧
         H h = none ∧ m.next ≤ d ∧ m.next ≤ m'.next ∧ MemModels m' (H.set h (d, [])) ∧
         (∀ al ∈ m.allocs, Keeps m m' al)) := by
  refine ⟨_, rfl, ?_⟩
  rcases newMapObj_spec hm [] with ht | ⟨h, m', d, he, h1, h2, h3, h4, h5, h6, h7⟩
  · left; simp [Res.toOutcome, ht]
  · right; exact ⟨h, m', d, by simp [Res.toOutcome, he, ret1], h1, h2, h3, h4, h5, h6, h7⟩

theorem spec_clone (hm : MemModels m H) (ctx hv : Val) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) (hh : hv.toNat = h) :
    ∃ f, mapEnv.extern "flat_map_clone" = some f ∧
      (f [ctx, hv] m = .trapped oomTrap ∨
       ∃ h' m' d', f [ctx, hv] m = .returned [Val.ofNat .i64 h'] m' ∧ m.next ≤ h' ∧ h' < 2 ^ 64 ∧
         H h' = none ∧ m.next ≤ d' ∧ m.next ≤ m'.next ∧ MemModels m' (H.set h' (d', es)) ∧
         (∀ al ∈ m.allocs, Keeps m m' al)) := by
  refine ⟨_, rfl, ?_⟩
  simp only [hh, hm.readEntries hH, Res.toOutcome]
  rcases newMapObj_spec hm es with ht | ⟨h', m', d', he, h1, h2, h3, h4, h5, h6, h7⟩
  · left; simp [ht]
  · right; exact ⟨h', m', d', by simp [he, ret1], h1, h2, h3, h4, h5, h6, h7⟩

theorem spec_contains (hm : MemModels m H) (ctx hv kv : Val) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) (hh : hv.toNat = h) :
    ∃ f, mapEnv.extern "flat_map_contains" = some f ∧
      f [ctx, hv, kv] m =
        .returned [Val.ofBool (DSL.Map.lookupL (BitVec.ofNat 64 kv.toNat) es).isSome] m := by
  refine ⟨_, rfl, ?_⟩
  simp [hh, hm.readEntries hH, Res.toOutcome, ret1]

theorem spec_insert (hm : MemModels m H) (ctx hv kv vv : Val) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) (hh : hv.toNat = h) :
    ∃ f, mapEnv.extern "flat_map_insert" = some f ∧
      (f [ctx, hv, kv, vv] m = .trapped oomTrap ∨
       ∃ m' d', f [ctx, hv, kv, vv] m = .returned [] m' ∧ m.next ≤ d' ∧ m.next ≤ m'.next ∧
         MemModels m' (H.set h (d',
           DSL.Map.upsertL (BitVec.ofNat 64 kv.toNat) (BitVec.ofNat 64 vv.toNat) es)) ∧
         (∀ al ∈ m.allocs, al.base ≠ h → Keeps m m' al)) := by
  refine ⟨_, rfl, ?_⟩
  simp only [hh, hm.readEntries hH, Res.toOutcome]
  have ho := hm.obj h d es hH
  rcases writeEntries_spec hm
      (DSL.Map.upsertL (BitVec.ofNat 64 kv.toNat) (BitVec.ofNat 64 vv.toNat) es) ho.hdr
      (fun h' d' es' hH' _ => (hm.sep h' d' es' h d es hH' hH).1) with
    ht | ⟨m', d', he, h1, h2, h3, h4⟩
  · left; simp [ht]
  · right; exact ⟨m', d', by simp [he], h1, h2, h3, h4⟩

/-- `flat_map_get` with the output cell in an allocation `al` that is no object piece. -/
theorem spec_get (hm : MemModels m H) (ctx hv kv out : Val) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) (hh : hv.toNat = h) {al : Alloc}
    (hal : al ∈ m.allocs) (hin : al.base ≤ out.toNat ∧ out.toNat + 8 ≤ al.base + al.size)
    (hfree : ObjFree H al.base) :
    ∃ f, mapEnv.extern "flat_map_get" = some f ∧
      match DSL.Map.lookupL (BitVec.ofNat 64 kv.toNat) es with
      | some w => f [ctx, hv, kv, out] m =
          .returned [Val.ofBool true] (m.writeBits false out.toNat 8 w)
      | none => f [ctx, hv, kv, out] m = .returned [Val.ofBool false] m := by
  refine ⟨_, rfl, ?_⟩
  simp only [hh, hm.readEntries hH, Res.toOutcome]
  split
  · rename_i w hw
    simp [hw, writeWord_eq w hal hin, ret1]
  · rename_i hw
    simp [hw, ret1]

/-! ## Keys and values as words in the generated code -/

theorem toWordV_run_w64 (vs : List ValueId) (cg : CG) :
    (toWordV (.int .w64) vs).run cg = (vs.headD 0, cg) := rfl

section
variable {E : Clif.Env} {P : Program}

theorem reach_toWordV {F : Function} {cg : CG} {s : State} {k : Ty} {vs : List ValueId}
    {v : Val} {x : k.denote} {H : Heap} {Q : State → Prop} {X : Outcome → Prop}
    (hk : k.isKey = true) (hG : Good F ((toWordV k vs).run cg).2) (hAt : At F cg s.frame)
    (hv : RegsHas s.frame.regs vs [v]) (hE : Enc H k x [v])
    (kont : ∀ fr' : Frame, At F ((toWordV k vs).run cg).2 fr' →
      fr'.regs ((toWordV k vs).run cg).1 = some (Val.ofNat .i64 (toWord k x).toNat) →
      Agree s.frame.regs fr'.regs cg.nextVal → ((toWordV k vs).run cg).2.nextVal ≤ cg.nextVal + 1 →
      cg.nextVal ≤ ((toWordV k vs).run cg).2.nextVal →
      (((toWordV k vs).run cg).1 < ((toWordV k vs).run cg).2.nextVal ∨
        ((toWordV k vs).run cg).1 ∈ vs) →
      fr'.func = s.frame.func → fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr' }) :
    Reach E P Q X s := by
  obtain ⟨y, rfl, hy⟩ := RegsHas.single_inv hv
  cases k with
  | int w =>
    simp only [Enc] at hE; cases hE
    cases w
    case w64 =>
      have := kont s.frame hAt (by
        simp only [toWordV_run_w64, List.headD_cons]; rw [hy]; simp [intV, toWord]; rfl)
        (Agree.refl _ _) (by simp [toWordV_run_w64]) (by simp [toWordV_run_w64])
        (.inr (by simp [toWordV_run_w64])) rfl rfl
      exact this
    all_goals
      refine reach_inst1 hG hAt (fun _ _ h => by cases h)
        (eval_uextend (w' := .w64) _ _ hy (by decide)) fun fr' hA hr hf hs => ?_
      refine kont fr' hA ?_ (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) (Nat.le_refl _)
        (Nat.le_succ _) (.inl (Nat.lt_succ_self _)) hf hs
      rw [hr]; simp [toWordV, inst1_run, intV, toWord, intTy, Clif.Ty.width]; rfl
  | bool =>
    simp only [Enc] at hE; cases hE
    have hev : evalInst s.frame s.mem (.extend .uextend .i64 y) =
        .ok ([Val.ofNat .i64 (toWord .bool x).toNat], s.mem) := by
      simp only [evalInst, get_of hy, Clif.Res.ok_bind]
      cases x <;> rfl
    refine reach_inst1 hG hAt (fun _ _ h => by cases h) hev fun fr' hA hr hf hs => ?_
    exact kont fr' hA (by rw [hr]; simp [toWordV, inst1_run]) (by rw [hr]; exact Agree.set _ (Nat.le_refl _))
      (Nat.le_refl _) (Nat.le_succ _) (.inl (Nat.lt_succ_self _)) hf hs
  | _ => simp [DSL.Ty.isKey] at hk

theorem ofWordV_run_w64 (x : ValueId) (cg : CG) :
    (ofWordV (.int .w64) x).run cg = ([x], cg) := rfl

theorem reach_ofWordV {F : Function} {cg : CG} {s : State} {k : Ty} {raw : ValueId}
    {x : k.denote} {Q : State → Prop} {X : Outcome → Prop}
    (hk : k.isKey = true) (hG : Good F ((ofWordV k raw).run cg).2) (hAt : At F cg s.frame)
    (hv : s.frame.regs raw = some ⟨.i64, toWord k x⟩)
    (kont : ∀ fr' : Frame, At F ((ofWordV k raw).run cg).2 fr' →
      (∀ H, ∃ v, RegsHas fr'.regs ((ofWordV k raw).run cg).1 [v] ∧ Enc H k x [v]) →
      Agree s.frame.regs fr'.regs cg.nextVal →
      cg.nextVal ≤ ((ofWordV k raw).run cg).2.nextVal →
      (∀ y ∈ ((ofWordV k raw).run cg).1, y < ((ofWordV k raw).run cg).2.nextVal ∨ y = raw) →
      fr'.func = s.frame.func → fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr' }) :
    Reach E P Q X s := by
  cases k with
  | int w =>
    cases w
    case w64 =>
      refine kont s.frame hAt (fun H => ⟨_, ?_, rfl⟩) (Agree.refl _ _) (by simp [ofWordV_run_w64])
        (fun y hy => .inr (by simpa [ofWordV_run_w64] using hy)) rfl rfl
      simp only [ofWordV_run_w64]
      exact RegsHas.single (by rw [hv]; simp [intV, toWord, Val.ofNat, Clif.Ty.width, intTy])
    all_goals
      refine reach_inst1 (v := intV _ x) (m' := s.mem) hG hAt (fun _ _ h => by cases h) ?_
        fun fr' hA hr hf hs => ?_
      · simp only [evalInst, get_of hv, Clif.Res.ok_bind]
        simp [intV, Val.ofNat, intTy, Clif.Ty.width, Clif.Sem.ireduce, Clif.Res.check, toWord]
        try (congr 1; apply BitVec.eq_of_toNat_eq; simp [IntW.bits]; omega)
      refine kont fr' hA (fun H => ⟨_, ?_, rfl⟩) (by rw [hr]; exact Agree.set _ (Nat.le_refl _))
        (Nat.le_succ _) (fun y hy => .inl ?_) hf hs
      · simp only [ofWordV, bind_run, inst1_run, pure_run]; rw [hr]
        exact RegsHas.set_same _ _ _
      · simp only [ofWordV, bind_run, inst1_run, pure_run] at hy ⊢; simp at hy; rw [hy]
        exact Nat.lt_succ_self _
  | bool =>
    have hev : evalInst s.frame s.mem (.ireduce .i8 raw) = .ok ([Val.ofBool x], s.mem) := by
      simp only [evalInst, get_of hv, Clif.Res.ok_bind]
      cases x <;> rfl
    refine reach_inst1 hG hAt (fun _ _ h => by cases h) hev fun fr' hA hr hf hs => ?_
    refine kont fr' hA (fun H => ⟨_, ?_, rfl⟩) (by rw [hr]; exact Agree.set _ (Nat.le_refl _))
      (Nat.le_succ _) (fun y hy => .inl ?_) hf hs
    · simp only [ofWordV, bind_run, inst1_run, pure_run]; rw [hr]
      exact RegsHas.set_same _ _ _
    · simp only [ofWordV, bind_run, inst1_run, pure_run] at hy ⊢; simp at hy; rw [hy]
      exact Nat.lt_succ_self _
  | _ => simp [DSL.Ty.isKey] at hk

end

end Compile.Proof
