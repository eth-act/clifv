import FV.Opt.Proof.LegalExt
import FV.Opt.Proof.LegalShift8
import FV.Opt.Proof.LegalShift16
import FV.Opt.Proof.LegalShift32
import FV.Opt.Proof.LegalShift64

/-!
# A statement with a pure plan

`pure_step`: when `planOf` gives a statement of `f` a pure plan (`.pure pat ins outs`) and the
statement evaluates, the target registers hold, at `ins`, input values on which the canonical
pattern `pat` runs, and its outputs, written at `outs`, represent the statement's results
(`OutsOk`). The per-instruction cases combine the source semantics (`evalInst`), the value
relation (`VRel`, `SrcInv`) and the pattern theorems (`LegalArith`, `LegalShift*`).
-/

namespace Opt.Legal

open Clif

/-! ## Helpers -/

/-- `ρ` holds the values `vs` at `xs`. -/
def Holds (ρ : Regs) : List ValueId → List Val → Prop
  | [], [] => True
  | x :: xs, v :: vs => ρ x = some v ∧ Holds ρ xs vs
  | _, _ => False

theorem Holds.len {ρ : Regs} : ∀ {xs : List ValueId} {vs : List Val}, Holds ρ xs vs →
    vs.length = xs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [h.len]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Holds.get {ρ : Regs} : ∀ {xs : List ValueId} {vs : List Val}, Holds ρ xs vs →
    ∀ i (hi : i < xs.length), ρ xs[i] = vs[i]?
  | [], [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _ :: _, ⟨h1, h2⟩, 0, _ => by simpa using h1
  | _ :: _, _ :: _, ⟨_, h2⟩, i + 1, hi => by simpa using h2.get i (by simpa using hi)
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- The source results `rs` with values `vals` are represented once the target holds the
canonical outputs of `ρ0` (from `nIn`) at `outs`. -/
def OutsOk (C : Ctx) (ρ0 : Regs) (nIn : Nat) (outs rs : List ValueId) (vals : List Val) : Prop :=
  ∀ ρ' : Regs, (∀ k (hk : k < outs.length) v, ρ0 (nIn + k) = some v → ρ' outs[k] = some v) →
    ∀ (i : Nat) (r : ValueId) (x : Val), rs[i]? = some r → vals[i]? = some x → RelV C ρ' r x

theorem split128 (X : BitVec 128) : X.extractLsb' 64 64 ++ X.extractLsb' 0 64 = X := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases hj2 : j < 64
  · simp [hj2]
  · simp [hj2, show j - 64 < 64 by omega]; exact congrArg _ (by omega)

theorem outsOk_pair {C : Ctx} {ρ0 : Regs} {n : Nat} {r rl rh : ValueId}
    (hp : C.pair r = some (rl, rh)) {X : BitVec 128} (hX : Out128 ρ0 n (n + 1) X) :
    OutsOk C ρ0 n [rl, rh] [r] [⟨.i128, X⟩] := by
  intro ρ' hρ i r' x hr hx
  cases i with
  | succ i => simp at hr
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hx
    subst hr hx
    rw [RelV.pair hp]
    refine ⟨X.extractLsb' 0 64, X.extractLsb' 64 64, by rw [split128], ?_, ?_⟩
    · exact hρ 0 (by simp) _ hX.1
    · exact hρ 1 (by simp) _ hX.2

theorem outsOk_plain {C : Ctx} {ρ0 : Regs} {n : Nat} {r : ValueId} (hp : C.pair r = none)
    {x : Val} (hx : ρ0 n = some x) : OutsOk C ρ0 n [r] [r] [x] := by
  intro ρ' hρ i r' x' hr hx'
  cases i with
  | succ i => simp at hr
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hx'
    subst hr hx'
    rw [RelV.plain hp]
    exact hρ 0 (by simp) _ hx

theorem outsOk_two {C : Ctx} {ρ0 : Regs} {n : Nat} {r0 r1 : ValueId} (hp0 : C.pair r0 = none)
    (hp1 : C.pair r1 = none) {x0 x1 : Val} (h0 : ρ0 n = some x0) (h1 : ρ0 (n + 1) = some x1) :
    OutsOk C ρ0 n [r0, r1] [r0, r1] [x0, x1] := by
  intro ρ' hρ i r' x' hr hx'
  match i, hr, hx' with
  | 0, hr, hx' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hx'
    subst hr hx'
    rw [RelV.plain hp0]
    exact hρ 0 (by simp) _ h0
  | 1, hr, hx' =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hr hx'
    subst hr hx'
    rw [RelV.plain hp1]
    exact hρ 1 (by simp) _ h1
  | i + 2, hr, _ => simp at hr

/-- Operands and results of a statement of `f` are values of `f` (below `T0`). -/
theorem ops_lt {C : Ctx} (hG : Good C) {B : Block} (hB : B ∈ C.f.blocks) {s : Stmt}
    (hs : s ∈ B.body) {x : ValueId} (hx : x ∈ instOps s.inst) : x < C.T0 :=
  hG.ids x (by
    simp only [idsOf, List.mem_flatMap, List.mem_append]
    exact ⟨B, hB, .inl (.inr ⟨s, hs, .inr hx⟩)⟩)

theorem res_lt {C : Ctx} (hG : Good C) {B : Block} (hB : B ∈ C.f.blocks) {s : Stmt}
    (hs : s ∈ B.body) {x : ValueId} (hx : x ∈ s.results) : x < C.T0 :=
  hG.ids x (by
    simp only [idsOf, List.mem_flatMap, List.mem_append]
    exact ⟨B, hB, .inl (.inr ⟨s, hs, .inl hx⟩)⟩)

theorem plain_iff {C : Ctx} {v : ValueId} : C.plain v = true ↔ C.pair v = none := by
  simp [Ctx.plain, Option.isNone_iff_eq_none]

/-- A paired source value is an `i128` value, its halves at the pair. -/
theorem pairVal {C : Ctx} {ρ ρ' : Regs} (hV : VRel C ρ ρ') {v a b : ValueId} (hv : v < C.T0)
    (hp : C.pair v = some (a, b)) {x : Val} (hx : ρ v = some x) :
    ∃ l h : BitVec 64, x = ⟨.i128, h ++ l⟩ ∧ ρ' a = some ⟨.i64, l⟩ ∧ ρ' b = some ⟨.i64, h⟩ :=
  hV.get_pair hv hp hx

theorem getAs_ok {fr : Frame} {x : ValueId} {t : Ty} {a : BitVec t.width}
    (h : fr.getAs x t = .ok a) : fr.regs x = some ⟨t, a⟩ := by
  simp only [Frame.getAs, Frame.get, Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok] at h
  obtain ⟨v, hv, h2⟩ := h
  obtain ⟨vt, vb⟩ := v
  simp only [Val.as?] at h2
  split at h2
  · rename_i heq
    subst heq
    simp only [Option.some.injEq] at h2
    subst h2
    exact hv
  · cases h2

theorem get_ok {fr : Frame} {x : ValueId} {v : Val} (h : fr.get x = .ok v) : fr.regs x = some v := by
  simpa [Frame.get] using h


theorem isShift_cases {op : BinaryOp} (h : op.isShift = true) :
    op = .ishl ∨ op = .ushr ∨ op = .sshr ∨ op = .rotl ∨ op = .rotr := by
  cases op <;> simp_all [BinaryOp.isShift]

/-- A source shift at `i128` is `shiftV` by the amount modulo 128. -/
theorem shift_eq {op : BinaryOp} (hop : op.isShift = true) {v : Nat} (a : BitVec 128)
    (b : BitVec v) : Sem.shift op a b = some (shiftV op a (b.toNat % 128)) := by
  rcases isShift_cases hop with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The constant-shift pattern computes the source shift (`rotr` normalised to `rotl`). -/
theorem shiftC_eq {op : BinaryOp} (hop : op.isShift = true) {n : Nat} (hn : n < 128)
    (X : BitVec 128) :
    shiftC (if (op == .rotr) = true then .rotl else op) X
      (if (op == .rotr) = true then (128 - n) % 128 else n) = shiftV op X n := by
  rcases isShift_cases hop with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [beq_self_eq_true, reduceCtorEq, beq_iff_eq, ite_true, ite_false,
    Bool.false_eq_true]
  all_goals try rfl
  exact (rotateRight_eq X hn).symm

theorem append_mod128 (yh yl : BitVec 64) : (yh ++ yl).toNat % 128 = yl.toNat % 128 := by
  rw [append_toNat]; omega

theorem append_lo (h l : BitVec 64) : (h ++ l).extractLsb' 0 64 = l := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, append_toNat]
  have := l.isLt
  simp only [Nat.shiftRight_zero]
  omega

theorem append_hi (h l : BitVec 64) : (h ++ l).extractLsb' 64 64 = h := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, append_toNat, Nat.shiftRight_eq_div_pow]
  have := l.isLt; have := h.isLt
  omega

theorem append_mod128' (yh yl : BitVec 64) :
    @BitVec.toNat Ty.i128.width (yh ++ yl) % 128 = yl.toNat % 128 := append_mod128 yh yl

theorem append_lo' (h l : BitVec 64) : @BitVec.extractLsb' Ty.i128.width 0 64 (h ++ l) = l :=
  append_lo h l

theorem append_hi' (h l : BitVec 64) : @BitVec.extractLsb' Ty.i128.width 64 64 (h ++ l) = h :=
  append_hi h l

theorem isplit_lo (h l : BitVec 64) :
    @BitVec.extractLsb' Ty.i128.width 0 Ty.i64.width (h ++ l) = l := append_lo h l

theorem isplit_hi (h l : BitVec 64) :
    @BitVec.extractLsb' Ty.i128.width Ty.i64.width Ty.i64.width (h ++ l) = h := append_hi h l

theorem out128_append (ρ : Regs) (a b : ValueId) (l h : BitVec 64)
    (ha : ρ a = some (V64 l)) (hb : ρ b = some (V64 h)) : Out128 ρ a b (h ++ l) := by
  refine ⟨?_, ?_⟩
  · rw [ha, append_lo]
  · rw [hb, append_hi]

theorem val_i128 {a : BitVec 128} {l h : BitVec 64}
    (he : (⟨.i128, a⟩ : Val) = ⟨.i128, h ++ l⟩) : a = h ++ l := by
  simpa using he

/-- The images of a pair result. -/
theorem outs_pair {C : Ctx} {r rl rh : ValueId} (hp : C.pair r = some (rl, rh)) :
    ∀ w ∈ [rl, rh], ∃ r' ∈ [r], w ∈ img C r' := by
  intro w hw; exact ⟨r, by simp, by simpa [img, hp] using hw⟩

theorem outs_plain {C : Ctx} {r : ValueId} (hp : C.pair r = none) :
    ∀ w ∈ [r], ∃ r' ∈ [r], w ∈ img C r' := by
  intro w hw
  simp only [List.mem_singleton] at hw; subst hw
  exact ⟨w, by simp, by simp [img, hp]⟩

theorem outs_two {C : Ctx} {r0 r1 : ValueId} (hp0 : C.pair r0 = none) (hp1 : C.pair r1 = none) :
    ∀ w ∈ [r0, r1], ∃ r' ∈ [r0, r1], w ∈ img C r' := by
  intro w hw
  refine ⟨w, hw, ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl <;> simp [img, hp0, hp1]

/-- The source value of a constant shift amount. -/
theorem constAmt_val {C : Ctx} {ρ : Regs} (hS : SrcInv C.f ρ) {y : ValueId} {b : Val}
    (hy : ρ y = some b) {n : Nat} (hc : constAmt C y = some n) :
    b.bits.toNat % 128 = n ∧ n < 128 := by
  obtain ⟨-, hk, hcc⟩ := hS y b hy
  unfold constAmt at hc
  split at hc
  · obtain ⟨c, hc1, rfl⟩ := Option.map_eq_some_iff.1 hc
    exact ⟨by rw [hk c hc1], Nat.mod_lt _ (by omega)⟩
  · obtain ⟨c, hc1, rfl⟩ := Option.map_eq_some_iff.1 hc
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    rw [← hcc c hc1, Nat.mod_mod_of_dvd _ (by decide)]

/-- The type of a source value is its static type. -/
theorem val_ty {C : Ctx} {ρ : Regs} (hS : SrcInv C.f ρ) {y : ValueId} {b : Val}
    (hy : ρ y = some b) {t : Ty} (ht : tyOf C.f y = some t) : ∃ bb, b = ⟨t, bb⟩ := by
  have h1 := (hS y b hy).1
  rw [ht] at h1
  simp only [reduceCtorEq, Option.some.injEq, false_or] at h1
  obtain ⟨bt, bb⟩ := b
  simp only at h1
  subst h1
  exact ⟨bb, rfl⟩

/-! ## The pure plans -/

/-- **A statement with a pure plan.** -/
theorem pure_step {C : Ctx} (hG : Good C) {B : Block} (hB : B ∈ C.f.blocks) {s : Stmt}
    (hs : s ∈ B.body) {pat : List Stmt} {ins outs : List ValueId}
    (hp : planOf C s = some (.pure pat ins outs)) {fr fr' : Frame}
    (hV : VRel C fr.regs fr'.regs) (hS : SrcInv C.f fr.regs) {m : Mem} {vals : List Val}
    {m' : Mem} (hev : evalInst fr m s.inst = .ok (vals, m')) :
    m' = m ∧ (∀ w ∈ outs, ∃ r ∈ s.results, w ∈ img C r) ∧
    ∃ inVals ρ0, Holds fr'.regs ins inVals ∧ runPat (canon inVals) pat = some ρ0 ∧
      OutsOk C ρ0 ins.length outs s.results vals := by
  have hop : ∀ x ∈ instOps s.inst, x < C.T0 := fun x hx => ops_lt hG hB hs hx
  obtain ⟨rs, inst⟩ := s
  simp only at hop hev ⊢
  unfold planOf at hp
  dsimp only at hp
  split at hp
  all_goals (try (simp [Option.bind_eq_some_iff] at hp; done))
  all_goals try simp only [instOps, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq] at hop
  case h_1 op x r =>
    -- unary
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.pure.injEq] at hp
    obtain ⟨⟨xl, xh⟩, hx, ⟨rl, rh⟩, hr, rfl, rfl, rfl⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
    obtain ⟨a, ha, rfl, rfl⟩ := hev
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨ρ0, hrun, hout⟩ := pat_unary op l h
    exact ⟨rfl, outs_pair hr, [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun, outsOk_pair hr hout⟩
  case h_2 op x y r =>
    -- binary at i128
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨xl, xh⟩, hx, ⟨rl, rh⟩, hr, hp⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok] at hev
    obtain ⟨a, ha, hev⟩ := hev
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop.1 hx (getAs_ok ha)
    cases val_i128 he
    by_cases hsh : op.isShift = true
    · rw [if_pos hsh] at hp hev
      simp only [Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok, Opt.Res.pure_eq_ok,
        Prod.mk.injEq] at hev
      obtain ⟨b, hb, res, hres, rfl, rfl⟩ := hev
      have hyv := get_ok hb
      have hres' : res = shiftV op (h ++ l) (b.bits.toNat % 128) :=
        Option.some.inj (hres.symm.trans (shift_eq hsh (h ++ l) b.bits))
      subst hres'
      split at hp
      · rename_i n hn
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        obtain ⟨hbn, hn128⟩ := constAmt_val hS hyv hn
        have hn' : (if (op == .rotr) = true then (128 - n) % 128 else n) < 128 := by
          split <;> omega
        obtain ⟨ρ0, hrun, hout⟩ := pat_constShift _ _ hn' l h
        rw [shiftC_eq hsh hn128] at hout
        rw [hbn]
        exact ⟨rfl, outs_pair hr, [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun,
          outsOk_pair hr hout⟩
      · split at hp
        · rename_i yl yh' hy
          simp only [Option.some.injEq, Plan.pure.injEq] at hp
          obtain ⟨rfl, rfl, rfl⟩ := hp
          obtain ⟨bl, bh, rfl, hbl, -⟩ := pairVal hV hop.2 hy hyv
          obtain ⟨ρ0, hrun, hout⟩ := pat_varShift64 op (isShift_cases hsh) l h bl
          refine ⟨rfl, outs_pair hr, [V64 l, V64 h, V64 bl], ρ0, ⟨hl, hh, hbl, trivial⟩, hrun, ?_⟩
          rw [append_mod128']
          exact outsOk_pair hr hout
        · rename_i hy
          have hby : fr'.regs y = some b := hV.get_plain hop.2 (plain_iff.2 hy) hyv
          split at hp
          · rename_i hty
            simp only [Option.some.injEq, Plan.pure.injEq] at hp
            obtain ⟨rfl, rfl, rfl⟩ := hp
            obtain ⟨bb, rfl⟩ := val_ty hS hyv hty
            obtain ⟨ρ0, hrun, hout⟩ := pat_varShift64 op (isShift_cases hsh) l h bb
            exact ⟨rfl, outs_pair hr, [V64 l, V64 h, V64 bb], ρ0, ⟨hl, hh, hby, trivial⟩, hrun,
              outsOk_pair hr hout⟩
          · rename_i hty
            simp only [Option.some.injEq, Plan.pure.injEq] at hp
            obtain ⟨rfl, rfl, rfl⟩ := hp
            obtain ⟨bb, rfl⟩ := val_ty hS hyv hty
            obtain ⟨ρ0, hrun, hout⟩ := pat_varShift8 op (isShift_cases hsh) l h bb
            exact ⟨rfl, outs_pair hr, [V64 l, V64 h, ⟨.i8, bb⟩], ρ0, ⟨hl, hh, hby, trivial⟩,
              hrun, outsOk_pair hr hout⟩
          · rename_i hty
            simp only [Option.some.injEq, Plan.pure.injEq] at hp
            obtain ⟨rfl, rfl, rfl⟩ := hp
            obtain ⟨bb, rfl⟩ := val_ty hS hyv hty
            obtain ⟨ρ0, hrun, hout⟩ := pat_varShift16 op (isShift_cases hsh) l h bb
            exact ⟨rfl, outs_pair hr, [V64 l, V64 h, ⟨.i16, bb⟩], ρ0, ⟨hl, hh, hby, trivial⟩,
              hrun, outsOk_pair hr hout⟩
          · rename_i hty
            simp only [Option.some.injEq, Plan.pure.injEq] at hp
            obtain ⟨rfl, rfl, rfl⟩ := hp
            obtain ⟨bb, rfl⟩ := val_ty hS hyv hty
            obtain ⟨ρ0, hrun, hout⟩ := pat_varShift32 op (isShift_cases hsh) l h bb
            exact ⟨rfl, outs_pair hr, [V64 l, V64 h, ⟨.i32, bb⟩], ρ0, ⟨hl, hh, hby, trivial⟩,
              hrun, outsOk_pair hr hout⟩
          · cases hp
    · rw [if_neg hsh] at hp hev
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨⟨yl, yh⟩, hy, pat', hpat, rfl, rfl, rfl⟩ := hp
      simp only [Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
      obtain ⟨b, hb, rfl, rfl⟩ := hev
      obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hV hop.2 hy (getAs_ok hb)
      cases val_i128 he2
      by_cases hm : op = .imul
      · subst hm
        have e : pat' = (Pat.binary .imul).getD [] := by rw [hpat]; rfl
        subst e
        obtain ⟨ρ0, hrun, hout⟩ := pat_imul l h bl bh
        exact ⟨rfl, outs_pair hr, [V64 l, V64 h, V64 bl, V64 bh], ρ0,
          ⟨hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_pair hr hout⟩
      · obtain ⟨ρ0, hrun, hout⟩ := pat_binary hpat hm l h bl bh
        exact ⟨rfl, outs_pair hr, [V64 l, V64 h, V64 bl, V64 bh], ρ0,
          ⟨hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_pair hr hout⟩
  case h_3 op t x y r ht =>
    -- a narrow shift by an i128 amount
    split at hp
    · rename_i yl yh' hy
      split at hp
      · rename_i hc
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨hsh, -⟩, hpx⟩, hpr⟩ := hc
        simp only [evalInst, Opt.Res.bind_eq_ok, hsh, ite_true, Opt.Res.ofOption_eq_ok,
          Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
        obtain ⟨a, ha, b, hb, res, hres, rfl, rfl⟩ := hev
        obtain ⟨bl, bh, rfl, hbl, -⟩ := pairVal hV hop.2 hy (get_ok hb)
        have hxa : fr'.regs x = some ⟨t, a⟩ := hV.get_plain hop.1 hpx (getAs_ok ha)
        have ht' : t = .i8 ∨ t = .i16 ∨ t = .i32 ∨ t = .i64 := by cases t <;> simp_all
        obtain ⟨ρ0, hrun, hout⟩ := pat_shiftNarrow op hsh t ht' a bl bh
        exact ⟨rfl, outs_plain (plain_iff.1 hpr), [⟨t, a⟩, V64 bl], ρ0, ⟨hxa, hbl, trivial⟩, hrun,
          outsOk_plain (plain_iff.1 hpr) (hout res hres)⟩
      · cases hp
    · split at hp <;> simp at hp
  case h_5 cc x y r =>
    -- icmp at i128
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨xl, xh⟩, hx, ⟨yl, yh⟩, hy, hp⟩ := hp
    split at hp
    · rename_i hpr
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
      obtain ⟨a, ha, b, hb, rfl, rfl⟩ := hev
      obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop.1 hx (getAs_ok ha)
      cases val_i128 he
      obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hV hop.2 hy (getAs_ok hb)
      cases val_i128 he2
      obtain ⟨ρ0, hrun, hout⟩ := pat_icmp cc l h bl bh
      exact ⟨rfl, outs_plain (plain_iff.1 hpr), [V64 l, V64 h, V64 bl, V64 bh], ρ0,
        ⟨hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_plain (plain_iff.1 hpr) hout⟩
    · cases hp
  case h_6 c x y r | h_7 c x y r =>
    -- select at i128
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨xl, xh⟩, hx, ⟨yl, yh⟩, hy, ⟨rl, rh⟩, hr, hp⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
    obtain ⟨cv, hcv, a, ha, b, hb, rfl, rfl⟩ := hev
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop.2.1 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hV hop.2.2 hy (getAs_ok hb)
    cases val_i128 he2
    split at hp
    · rename_i cl ch hc
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨c0, c1, rfl, hcl, hch⟩ := pairVal hV hop.1 hc (get_ok hcv)
      obtain ⟨ρ0, hrun, hout⟩ := pat_select128c c0 c1 l h bl bh
      exact ⟨rfl, outs_pair hr, [V64 c0, V64 c1, V64 l, V64 h, V64 bl, V64 bh], ρ0,
        ⟨hcl, hch, hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_pair hr hout⟩
    · rename_i hc
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      have hcv' := hV.get_plain hop.1 (plain_iff.2 hc) (get_ok hcv)
      obtain ⟨ρ0, hrun, hout⟩ := pat_select128 cv l h bl bh
      exact ⟨rfl, outs_pair hr, [cv, V64 l, V64 h, V64 bl, V64 bh], ρ0,
        ⟨hcv', hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_pair hr hout⟩
  case h_8 t c x y r ht | h_9 t c x y r ht =>
    -- a narrow select with an i128 condition
    split at hp
    · rename_i cl ch hc
      split at hp
      · rename_i hcond
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
        obtain ⟨⟨⟨-, hpx⟩, hpy⟩, hpr⟩ := hcond
        simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
        obtain ⟨cv, hcv, a, ha, b, hb, rfl, rfl⟩ := hev
        obtain ⟨c0, c1, rfl, hcl, hch⟩ := pairVal hV hop.1 hc (get_ok hcv)
        have hxa := hV.get_plain hop.2.1 hpx (getAs_ok ha)
        have hyb := hV.get_plain hop.2.2 hpy (getAs_ok hb)
        obtain ⟨ρ0, hrun, hout⟩ := pat_selectc t c0 c1 a b
        exact ⟨rfl, outs_plain (plain_iff.1 hpr), [V64 c0, V64 c1, ⟨t, a⟩, ⟨t, b⟩], ρ0,
          ⟨hcl, hch, hxa, hyb, trivial⟩, hrun, outsOk_plain (plain_iff.1 hpr) hout⟩
      · cases hp
    · split at hp <;> simp at hp
  case h_10 c x y r =>
    -- bitselect at i128
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.pure.injEq] at hp
    obtain ⟨⟨cl, ch⟩, hc, ⟨xl, xh⟩, hx, ⟨yl, yh⟩, hy, ⟨rl, rh⟩, hr, rfl, rfl, rfl⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
    obtain ⟨cv, hcv, a, ha, b, hb, rfl, rfl⟩ := hev
    obtain ⟨c0, c1, he0, hcl, hch⟩ := pairVal hV hop.1 hc (getAs_ok hcv)
    cases val_i128 he0
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop.2.1 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hV hop.2.2 hy (getAs_ok hb)
    cases val_i128 he2
    obtain ⟨ρ0, hrun, hout⟩ := pat_bitselect c0 c1 l h bl bh
    exact ⟨rfl, outs_pair hr, [V64 c0, V64 c1, V64 l, V64 h, V64 bl, V64 bh], ρ0,
      ⟨hcl, hch, hl, hh, hbl, hbh, trivial⟩, hrun, outsOk_pair hr hout⟩
  case h_11 x r =>
    -- bmask at i128
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨rl, rh⟩, hr, hp⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
    obtain ⟨a, ha, rfl, rfl⟩ := hev
    split at hp
    · rename_i xl xh hx
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨l, h, rfl, hl, hh⟩ := pairVal hV hop hx (get_ok ha)
      obtain ⟨ρ0, hrun, hout⟩ := pat_bmask128c l h
      exact ⟨rfl, outs_pair hr, [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun,
        outsOk_pair hr hout⟩
    · rename_i hx
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      have hxa := hV.get_plain hop (plain_iff.2 hx) (get_ok ha)
      obtain ⟨ρ0, hrun, hout⟩ := pat_bmask128 a
      exact ⟨rfl, outs_pair hr, [a], ρ0, ⟨hxa, trivial⟩, hrun, outsOk_pair hr hout⟩
  case h_12 t x r ht =>
    -- a narrow bmask of an i128 value
    split at hp
    · rename_i xl xh hx
      split at hp
      · rename_i hpr
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
        obtain ⟨a, ha, rfl, rfl⟩ := hev
        obtain ⟨l, h, rfl, hl, hh⟩ := pairVal hV hop hx (get_ok ha)
        obtain ⟨ρ0, hrun, hout⟩ := pat_bmaskc t l h
        exact ⟨rfl, outs_plain (plain_iff.1 hpr), [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun,
          outsOk_plain (plain_iff.1 hpr) hout⟩
      · cases hp
    · split at hp <;> simp at hp
  case h_13 op x r =>
    -- extend to i128
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨rl, rh⟩, hr, hp⟩ := hp
    split at hp
    · rename_i hpx
      simp only [evalInst, Opt.Res.bind_eq_ok] at hev
      obtain ⟨a, ha, u, hu, hev⟩ := hev
      have hxa := hV.get_plain hop hpx (get_ok ha)
      split at hp
      · rename_i hty
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        obtain ⟨bb, rfl⟩ := val_ty hS (get_ok ha) hty
        obtain ⟨ρ0, hrun, hout⟩ := pat_extend64 op bb
        cases op <;> simp only [Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev <;>
          obtain ⟨rfl, rfl⟩ := hev <;>
          exact ⟨rfl, outs_pair hr, [V64 bb], ρ0, ⟨hxa, trivial⟩, hrun, outsOk_pair hr hout⟩
      · rename_i hty
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        obtain ⟨bb, rfl⟩ := val_ty hS (get_ok ha) hty
        obtain ⟨ρ0, hrun, hout⟩ := pat_extend8 op bb
        cases op <;> simp only [Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev <;>
          obtain ⟨rfl, rfl⟩ := hev <;>
          exact ⟨rfl, outs_pair hr, [⟨.i8, bb⟩], ρ0, ⟨hxa, trivial⟩, hrun, outsOk_pair hr hout⟩
      · rename_i hty
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        obtain ⟨bb, rfl⟩ := val_ty hS (get_ok ha) hty
        obtain ⟨ρ0, hrun, hout⟩ := pat_extend16 op bb
        cases op <;> simp only [Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev <;>
          obtain ⟨rfl, rfl⟩ := hev <;>
          exact ⟨rfl, outs_pair hr, [⟨.i16, bb⟩], ρ0, ⟨hxa, trivial⟩, hrun, outsOk_pair hr hout⟩
      · rename_i hty
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        obtain ⟨bb, rfl⟩ := val_ty hS (get_ok ha) hty
        obtain ⟨ρ0, hrun, hout⟩ := pat_extend32 op bb
        cases op <;> simp only [Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev <;>
          obtain ⟨rfl, rfl⟩ := hev <;>
          exact ⟨rfl, outs_pair hr, [⟨.i32, bb⟩], ρ0, ⟨hxa, trivial⟩, hrun, outsOk_pair hr hout⟩
      · cases hp
    · cases hp
  case h_14 t x r =>
    -- ireduce of an i128 value
    split at hp
    · rename_i xl xh hx
      split at hp
      · rename_i hpr
        simp only [Option.some.injEq, Plan.pure.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
        obtain ⟨a, ha, u, hu, rfl, rfl⟩ := hev
        obtain ⟨l, h, rfl, hl, -⟩ := pairVal hV hop hx (get_ok ha)
        have ht : t.width < 128 := by
          simp only [Res.check] at hu
          split at hu
          · rename_i hw; exact of_decide_eq_true hw
          · cases hu
        obtain ⟨ρ0, hrun, hout⟩ := pat_ireduce t ht l h
        exact ⟨rfl, outs_plain (plain_iff.1 hpr), [V64 l], ρ0, ⟨hl, trivial⟩, hrun,
          outsOk_plain (plain_iff.1 hpr) hout⟩
      · cases hp
    · split at hp <;> simp at hp
  case h_15 lo hi r =>
    -- iconcat of two i64 values
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨rl, rh⟩, hr, hp⟩ := hp
    split at hp
    · rename_i hc
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      simp only [Bool.and_eq_true] at hc
      simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok, Opt.Res.pure_eq_ok,
        Prod.mk.injEq, Ty.double?, Option.some.injEq] at hev
      obtain ⟨t2, rfl, l, hl0, h, hh0, rfl, rfl⟩ := hev
      have hl := hV.get_plain hop.1 hc.1 (getAs_ok hl0)
      have hh := hV.get_plain hop.2 hc.2 (getAs_ok hh0)
      obtain ⟨ρ0, hrun, h2, h3⟩ := pat_copy2 l h
      refine ⟨rfl, outs_pair hr, [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun, ?_⟩
      have e : (Sem.iconcat l h).setWidth Ty.i128.width = h ++ l := by
        simp [Sem.iconcat]
      rw [e]
      exact outsOk_pair hr (out128_append ρ0 2 3 l h h2 h3)
    · cases hp
  case h_16 x r0 r1 =>
    -- isplit of an i128 value
    simp only [bind, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨xl, xh⟩, hx, hp⟩ := hp
    split at hp
    · rename_i hc
      simp only [Option.some.injEq, Plan.pure.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      simp only [Bool.and_eq_true] at hc
      simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok, Opt.Res.pure_eq_ok,
        Prod.mk.injEq, Ty.half?, Option.some.injEq] at hev
      obtain ⟨t2, rfl, a, ha, rfl, rfl⟩ := hev
      obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop hx (getAs_ok ha)
      cases val_i128 he
      obtain ⟨ρ0, hrun, h2, h3⟩ := pat_copy2 l h
      refine ⟨rfl, outs_two (plain_iff.1 hc.1) (plain_iff.1 hc.2), [V64 l, V64 h], ρ0,
        ⟨hl, hh, trivial⟩, hrun, ?_⟩
      simp only [Sem.isplit]
      rw [isplit_lo, isplit_hi]
      exact outsOk_two (plain_iff.1 hc.1) (plain_iff.1 hc.2) h2 h3
    · cases hp
  case h_17 flags x r =>
    -- bitcast at i128
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.pure.injEq] at hp
    obtain ⟨⟨xl, xh⟩, hx, ⟨rl, rh⟩, hr, rfl, rfl, rfl⟩ := hp
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev
    obtain ⟨a, ha, rfl, rfl⟩ := hev
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hV hop hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨ρ0, hrun, h2, h3⟩ := pat_copy2 l h
    exact ⟨rfl, outs_pair hr, [V64 l, V64 h], ρ0, ⟨hl, hh, trivial⟩, hrun,
      outsOk_pair hr (out128_append ρ0 2 3 l h h2 h3)⟩
  all_goals (split at hp <;> simp at hp)

theorem ofOption_ne_trap {α : Type} (msg : String) (o : Option α) (c : TrapCode) :
    Res.ofOption msg o ≠ .trap c := by
  cases o <;> simp [Res.ofOption]

theorem getAs_ne_trap (fr : Frame) (x : ValueId) (t : Ty) (c : TrapCode) :
    fr.getAs x t ≠ .trap c := by
  simp [Frame.getAs, Frame.get, Opt.Res.bind_eq_trap, ofOption_ne_trap]

theorem get_ne_trap (fr : Frame) (x : ValueId) (c : TrapCode) : fr.get x ≠ .trap c :=
  ofOption_ne_trap _ _ c

theorem check_ne_trap (b : Bool) (msg : String) (c : TrapCode) : Res.check b msg ≠ .trap c := by
  unfold Res.check; split <;> simp

theorem pure_ne_trap {α : Type} (a : α) (c : TrapCode) : (pure a : Res α) ≠ .trap c := by
  simp [pure]

/-- A statement with a pure plan does not trap. -/
theorem pure_notrap {C : Ctx} {s : Stmt} {pat : List Stmt} {ins outs : List ValueId}
    (hp : planOf C s = some (.pure pat ins outs)) (fr : Frame) (m : Mem) (c : TrapCode) :
    evalInst fr m s.inst ≠ .trap c := by
  obtain ⟨rs, inst⟩ := s
  unfold planOf at hp
  dsimp only at hp
  intro h
  split at hp
  all_goals (try (simp [Option.bind_eq_some_iff] at hp; done))
  all_goals simp only [evalInst, Opt.Res.bind_eq_trap, getAs_ne_trap, get_ne_trap,
    ofOption_ne_trap, check_ne_trap, pure_ne_trap, false_or, exists_and_left, and_false,
    exists_false, or_false, false_and, exists_const] at h
  all_goals first
    | (split at hp <;> simp at hp; done)
    | exact getAs_ne_trap _ _ _ _ h.2
    | (obtain ⟨a, -, h⟩ := h
       split at h <;>
         simp only [Opt.Res.bind_eq_trap, get_ne_trap, ofOption_ne_trap, pure_ne_trap,
           getAs_ne_trap, false_or, reduceCtorEq, and_false, exists_false] at h)

end Opt.Legal
