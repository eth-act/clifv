import FV.Opt.Proof.MidValFold
import FV.Opt.Proof.MidValPhi

/-!
# Division by a constant is simulated by its input (#1119, `skeleton-removed div`)

`Opt.MidVal.divPre f bs` (`FV/Opt/MidValFold.lean`) rewrites, in the blocks `bs`, each
`v = op ty x y` whose divisor `y` has a constant in `K = kLook f.freshValue (kTable f)`
(checked by `kOk`, as for branch folding) into pure statements (`divRw`): `udiv`/`sdiv` by 1 into
`imul x, y`, `urem` by 1 into `iconst 0`, `udiv` by `2^k` into `s = iconst k; ushr x, s`, `urem`
by `2^k` into `s = iconst 2^k-1; band x, s`. The inserted values `s` come from a supply `S` of
values below `f.freshValue` that `f` neither defines nor reads (`supplyOk`), and the rewritten
function keeps `f`'s fresh value. Here: **`divPre_simU : FunSimU f (divPre f bs)`** and
**`foldPre_simU : FunSimU f (foldPre f bs)`** (`foldPre f bs = ConstPhi.run (foldBr (divPre
(phiPre f) bs) bs)`, `phiPre_simU`: `FV/Opt/Proof/MidValPhi.lean`).

The frame relation `DR`: the same point of a block of `f`, the rewritten frame running the
rewritten rest of that block's body (`BodyRel`), registers agreeing outside `S`, the same slots
and terminator, and `KInv` in `f`'s frame (the divisor holds its constant or nothing). At a
rewritten division the source steps once (it cannot trap: the divisor is a non-zero constant)
and the rewritten frame runs its one or two statements to the same value (`udiv_one`,
`sdiv_one`, `umod_one`, `udiv_twoPow_eq_of_lt`, `and_two_pow_sub_one_eq_mod`).
-/

namespace Opt.MidVal

open Clif

/-! ## Values -/

theorem log2Exact_spec {n k : Nat} (h : log2Exact n = some k) : 2 ^ k = n := by
  unfold log2Exact at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simpa using hc
  · cases h

theorem ty_width_ge (ty : Ty) : 8 ≤ ty.width := by cases ty <;> decide

theorem getAs_regs {fr : Frame} {x : ValueId} {t : Ty} {a : BitVec t.width}
    (h : fr.getAs x t = .ok a) : fr.regs x = some ⟨t, a⟩ := by
  simp only [Frame.getAs, Frame.get, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
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

theorem getAs_of_regs {fr : Frame} {x : ValueId} {t : Ty} {a : BitVec t.width}
    (h : fr.regs x = some ⟨t, a⟩) : fr.getAs x t = .ok a := by
  simp [Frame.getAs, Frame.get, h, Res.ofOption]
  try rfl

/-- The divisor `2 ^ k` of a width-`w` value: `k < w` and it is `twoPow w k`. -/
theorem twoPow_of_toNat {w k : Nat} {b : BitVec w} (h : b.toNat = 2 ^ k) :
    k < w ∧ b = BitVec.twoPow w k := by
  have hlt : k < w := by
    have h1 : 2 ^ k < 2 ^ w := h ▸ b.isLt
    exact (Nat.pow_lt_pow_iff_right (by decide)).1 h1
  refine ⟨hlt, BitVec.eq_of_toNat_eq ?_⟩
  rw [h, BitVec.toNat_twoPow_eq_ite, if_pos hlt]

theorem udiv_pow2 {w k : Nat} (a : BitVec w) (hk : k < w) :
    a / BitVec.twoPow w k = Sem.ushr a (BitVec.ofNat w k) := by
  rw [BitVec.udiv_twoPow_eq_of_lt hk]
  unfold Sem.ushr Sem.shiftAmt
  have h1 : (BitVec.ofNat w k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)
  rw [h1, Nat.mod_eq_of_lt hk]

theorem urem_pow2 {w k : Nat} (a : BitVec w) (hk : k < w) :
    a % BitVec.twoPow w k = Sem.band a (BitVec.ofNat w (2 ^ k - 1)) := by
  unfold Sem.band
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ k < 2 ^ w := (Nat.pow_lt_pow_iff_right (by decide)).2 hk
  have h0 := Nat.two_pow_pos w
  rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_twoPow_eq_ite,
    if_pos hk, Nat.mod_eq_of_lt (a := 2 ^ k - 1) (b := 2 ^ w) (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

theorem one_of_toNat {w : Nat} {b : BitVec w} (hw : 2 ≤ w) (h : b.toNat = 1) : b = 1#w := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hw)

theorem bv_one_ne_zero {w : Nat} (hw : 1 ≤ w) : (1#w) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at this
  rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))] at this
  cases this

theorem bv_ne_zero_of_toNat {w k : Nat} {b : BitVec w} (h : b.toNat = 2 ^ k) : b ≠ 0 := by
  intro h0
  have : b.toNat = 0 := by rw [h0]; rfl
  rw [h] at this
  exact Nat.ne_of_gt (Nat.two_pow_pos k) this

theorem bv_one_ne_allOnes {w : Nat} (hw : 2 ≤ w) : (1#w) ≠ BitVec.allOnes w := by
  intro h1
  have := congrArg BitVec.toNat h1
  have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  rw [BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem ofOption_ne_trap' {α : Type} (msg : String) (o : Option α) (c : TrapCode) :
    Res.ofOption msg o ≠ .trap c := by
  cases o <;> simp [Res.ofOption]

theorem getAs_ne_trap (fr : Frame) (x : ValueId) (t : Ty) (c : TrapCode) :
    fr.getAs x t ≠ .trap c := by
  intro h
  simp only [Frame.getAs, Frame.get, Res.bind_eq_trap] at h
  rcases h with h | ⟨v, -, h⟩
  · exact ofOption_ne_trap' _ _ _ h
  · exact ofOption_ne_trap' _ _ _ h

theorem ofExcept_ok {α : Type} {e : Except TrapCode α} {r : α} (h : Res.ofExcept e = .ok r) :
    e = .ok r := by
  cases e with
  | error c => simp [Res.ofExcept] at h
  | ok v => simp only [Res.ofExcept, Res.ok.injEq] at h; rw [h]

/-! ## The rewrite -/

/-- What `divRw` does with a statement it rewrites. -/
theorem divRw_spec {K : ValueId → Option Val} {s : ValueId} {st : Stmt} {xs : List Stmt}
    {u : Bool} (h : divRw K s st = some (xs, u)) :
    ∃ v op ty x y c k, st = ⟨[v], .div op ty x y⟩ ∧ K y = some c ∧ c.ty = ty ∧
      2 ^ k = c.bits.toNat ∧
      ((k = 0 ∧ op = .urem ∧ xs = [⟨[v], .iconst ty 0⟩] ∧ u = false) ∨
       (k = 0 ∧ (op = .udiv ∨ op = .sdiv) ∧ xs = [⟨[v], .binary .imul ty x y⟩] ∧ u = false) ∨
       (op = .udiv ∧ xs = [⟨[s], .iconst ty (BitVec.ofNat _ k)⟩, ⟨[v], .binary .ushr ty x s⟩] ∧
         u = true) ∨
       (op = .urem ∧ xs = [⟨[s], .iconst ty (BitVec.ofNat _ (2 ^ k - 1))⟩,
         ⟨[v], .binary .band ty x s⟩] ∧ u = true)) := by
  obtain ⟨rs, i⟩ := st
  unfold divRw at h
  split at h
  · rename_i v op ty x y hr hi
    simp only at hr hi
    subst hr hi
    split at h
    · rename_i c hc
      split at h
      · rename_i k hk
        have hk' := log2Exact_spec hk
        split at h
        · cases h
        · rename_i hty
          have hty' : c.ty = ty := Classical.not_not.1 hty
          refine ⟨v, op, ty, x, y, c, k, rfl, hc, hty', hk', ?_⟩
          split at h
          · rename_i hk0
            split at h
            · rename_i hop
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              exact .inl ⟨hk0, hop, h.1.symm, h.2.symm⟩
            · split at h
              · rename_i _ hop
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                exact .inr (.inl ⟨hk0, hop, h.1.symm, h.2.symm⟩)
              · cases h
          · split at h
            · rename_i _ hop
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              exact .inr (.inr (.inl ⟨hop, h.1.symm, h.2.symm⟩))
            · split at h
              · rename_i _ _ hop
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                exact .inr (.inr (.inr ⟨hop, h.1.symm, h.2.symm⟩))
              · cases h
      · cases h
    · cases h
  · cases h

/-- The rest of the supply is part of the supply. -/
theorem divBody_supply {K : ValueId → Option Val} :
    ∀ (ss : List Stmt) (sup : List ValueId), ∀ s ∈ (divBody K ss sup).2, s ∈ sup
  | [], sup, s, hs => hs
  | st :: ss, sup, s, hs => by
    unfold divBody at hs
    split at hs
    · rename_i a sup'
      split at hs
      · exact List.mem_cons_of_mem _ (divBody_supply ss sup' s hs)
      · exact divBody_supply ss _ s hs
      · exact divBody_supply ss _ s hs
    · split at hs
      · exact divBody_supply ss [] s hs
      · exact divBody_supply ss [] s hs

section
variable (K : ValueId → Option Val) (S : List ValueId)

/-- `yb` is `xb`, or `xb` rewritten with a supply from `S`. -/
def BodyRel (xb yb : List Stmt) : Prop :=
  yb = xb ∨ ∃ sup : List ValueId, (∀ s ∈ sup, s ∈ S) ∧ yb = (divBody K xb sup).1

/-- A block and its rewritten copy. -/
def BlockRel (B B' : Block) : Prop :=
  B'.id = B.id ∧ B'.params = B.params ∧ B'.term = B.term ∧ BodyRel K S B.body B'.body

end

theorem bodyRel_nil {K : ValueId → Option Val} {S : List ValueId} {yb : List Stmt}
    (h : BodyRel K S [] yb) : yb = [] := by
  rcases h with h | ⟨sup, -, h⟩
  · exact h
  · rw [h]; rfl

theorem bodyRel_cons {K : ValueId → Option Val} {S : List ValueId} {st : Stmt} {ss yb : List Stmt}
    (h : BodyRel K S (st :: ss) yb) :
    (∃ yr, yb = st :: yr ∧ BodyRel K S ss yr) ∨
    (∃ s xs u yr, divRw K s st = some (xs, u) ∧ (u = true → s ∈ S) ∧ yb = xs ++ yr ∧
      BodyRel K S ss yr) := by
  rcases h with h | ⟨sup, hsup, h⟩
  · exact .inl ⟨ss, h, .inl rfl⟩
  · unfold divBody at h
    split at h
    · rename_i a sup'
      split at h
      · rename_i xs hw
        exact .inr ⟨a, xs, true, _, hw, fun _ => hsup a (List.mem_cons_self ..), h,
          .inr ⟨sup', fun s hs => hsup s (List.mem_cons_of_mem _ hs), rfl⟩⟩
      · rename_i xs hw
        exact .inr ⟨a, xs, false, _, hw, (by intro h; cases h), h, .inr ⟨_, hsup, rfl⟩⟩
      · exact .inl ⟨_, h, .inr ⟨_, hsup, rfl⟩⟩
    · split at h
      · rename_i xs hw
        exact .inr ⟨0, xs, false, _, hw, (by intro h; cases h), h,
          .inr ⟨[], (by intro s hs; cases hs), rfl⟩⟩
      · exact .inl ⟨_, h, .inr ⟨[], (by intro s hs; cases hs), rfl⟩⟩

theorem divBlocks_find {K : ValueId → Option Val} {bs : List BlockId} {S : List ValueId}
    (id : BlockId) :
    ∀ (bl : List Block) (sup : List ValueId), (∀ s ∈ sup, s ∈ S) →
      match bl.find? (·.id == id) with
      | none => (divBlocks K bs bl sup).find? (·.id == id) = none
      | some B => ∃ B', (divBlocks K bs bl sup).find? (·.id == id) = some B' ∧ BlockRel K S B B'
  | [], _, _ => rfl
  | b :: rest, sup, hsup => by
    have ih := divBlocks_find (K := K) (bs := bs) (S := S) id rest
    by_cases hb : (b.id == id) = true
    · have hfb : (b :: rest).find? (·.id == id) = some b := by simp [List.find?_cons, hb]
      rw [hfb]
      by_cases hc : bs.contains b.id = true
      · refine ⟨{ b with body := (divBody K b.body sup).1 }, ?_, rfl, rfl, rfl,
          .inr ⟨sup, hsup, rfl⟩⟩
        simp [divBlocks, List.contains_iff_mem.1 hc, List.find?_cons, hb]
      · refine ⟨b, ?_, rfl, rfl, rfl, .inl rfl⟩
        have hc' : b.id ∉ bs := fun h => hc (List.contains_iff_mem.2 h)
        simp [divBlocks, hc', List.find?_cons, hb]
    · have hb' : (b.id == id) = false := by simpa using hb
      have hfb : (b :: rest).find? (·.id == id) = rest.find? (·.id == id) := by
        simp [List.find?_cons, hb']
      rw [hfb]
      by_cases hc : bs.contains b.id = true
      · have hd : (divBlocks K bs (b :: rest) sup).find? (·.id == id) =
            (divBlocks K bs rest (divBody K b.body sup).2).find? (·.id == id) := by
          simp [divBlocks, List.contains_iff_mem.1 hc, List.find?_cons, hb']
        rw [hd]
        exact ih _ (fun s hs => hsup s (divBody_supply _ _ s hs))
      · have hd : (divBlocks K bs (b :: rest) sup).find? (·.id == id) =
            (divBlocks K bs rest sup).find? (·.id == id) := by
          have hc' : b.id ∉ bs := fun h => hc (List.contains_iff_mem.2 h)
          simp [divBlocks, hc', List.find?_cons, hb']
        rw [hd]
        exact ih _ hsup

theorem divBlocks_head {K : ValueId → Option Val} {bs : List BlockId} {S : List ValueId}
    {bl : List Block} {sup : List ValueId} (hsup : ∀ s ∈ sup, s ∈ S) {B : Block}
    (h : bl.head? = some B) :
    ∃ B', (divBlocks K bs bl sup).head? = some B' ∧ BlockRel K S B B' := by
  cases bl with
  | nil => cases h
  | cons b rest =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    unfold divBlocks
    split
    · exact ⟨_, rfl, rfl, rfl, rfl, .inr ⟨sup, hsup, rfl⟩⟩
    · exact ⟨_, rfl, rfl, rfl, rfl, .inl rfl⟩

/-! ## The frame relation -/

section
variable {f : Function} {K : ValueId → Option Val} {bs : List BlockId} {S : List ValueId}

@[simp] theorem divFn_globals : (divFn f K bs S).globals = f.globals := rfl
@[simp] theorem divFn_externs : (divFn f K bs S).externs = f.externs := rfl
@[simp] theorem divFn_sig : (divFn f K bs S).sig = f.sig := rfl
@[simp] theorem divFn_sigDecls : (divFn f K bs S).sigDecls = f.sigDecls := rfl
@[simp] theorem divFn_slots : (divFn f K bs S).slots = f.slots := rfl
@[simp] theorem divFn_name : (divFn f K bs S).name = f.name := rfl

theorem divFn_block? (hsup : ∀ s ∈ S, s ∈ S) {id : BlockId} {B : Block}
    (h : f.block? id = some B) :
    ∃ B', (divFn f K bs S).block? id = some B' ∧ BlockRel K S B B' := by
  have := divBlocks_find (K := K) (bs := bs) (S := S) id f.blocks S hsup
  unfold Function.block? at h
  rw [h] at this
  exact this

theorem mem_usedVals {b : Block} (hb : b ∈ f.blocks) :
    (∀ p ∈ b.params, p.1 ∈ usedVals f) ∧
    (∀ st ∈ b.body, (∀ v ∈ st.results, v ∈ usedVals f) ∧ ∀ v ∈ operands st.inst, v ∈ usedVals f) ∧
    ∀ v ∈ termOperands b.term, v ∈ usedVals f := by
  refine ⟨fun p hp => ?_, fun st hst => ⟨fun v hv => ?_, fun v hv => ?_⟩, fun v hv => ?_⟩ <;>
    simp only [usedVals, List.mem_flatMap, List.mem_append, List.mem_map] <;>
    refine ⟨b, hb, ?_⟩
  · exact .inl (.inl ⟨p, hp, rfl⟩)
  · exact .inl (.inr ⟨st, hst, .inl hv⟩)
  · exact .inl (.inr ⟨st, hst, .inr hv⟩)
  · exact .inr hv

variable (f K bs S) in
/-- The frame relation (module doc). -/
def DR (X Y : Frame) : Prop :=
  X.func = f ∧ Y.func = divFn f K bs S ∧ KInv K X.regs ∧ Y.slots = X.slots ∧
    Agree (· ∉ S) X.regs Y.regs ∧ Y.term = X.term ∧
    ∃ b ∈ f.blocks, X.body <:+ b.body ∧ X.term = b.term ∧ BodyRel K S X.body Y.body

/-- The facts about the supply. -/
structure SupOk (f : Function) (S : List ValueId) : Prop where
  lt : ∀ s ∈ S, s < f.freshValue
  unused : ∀ s ∈ S, s ∉ usedVals f

theorem supOk_of {f : Function} {S : List ValueId} (h : supplyOk f S = true) : SupOk f S := by
  simp only [supplyOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun s hs => (h s hs).1, fun s hs hm => ?_⟩
  have h2 := (h s hs).2
  rw [List.contains_iff_mem.2 hm] at h2
  simp at h2

theorem notS_of_used {f : Function} {S : List ValueId} (hS : SupOk f S) {v : ValueId}
    (hv : v ∈ usedVals f) : v ∉ S := fun h => hS.unused v h hv

/-- Entering a block: its rewritten copy, registers agreeing outside `S`. -/
theorem DR.enter (hk : kOk f K = true) (hS : SupOk f S) {A A1 B : Frame} {bc : BlockCall}
    (hA : A.func = f) (hB : B.func = divFn f K bs S) (hI : KInv K A.regs)
    (hsl : B.slots = A.slots) (hag : Agree (· ∉ S) A.regs B.regs)
    (hargs : ∀ a ∈ bc.args, a ∉ S) (he : enterBlock A bc = .ok A1) :
    ∃ B1, enterBlock B bc = .ok B1 ∧ DR f K bs S A1 B1 := by
  obtain ⟨Bk, args, regs, hBk, hga, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hA] at hBk
  obtain ⟨Bk', hBk', hid, hpar, hterm, hbody⟩ := divFn_block? (K := K) (bs := bs) (fun s hs => hs) hBk
  have hBm : Bk ∈ f.blocks := List.mem_of_find?_eq_some hBk
  have hga' : B.getMany bc.args = .ok args := by
    rw [getMany_congr (fr := A) (fr' := B) (fun x hx => hag x (hargs x hx))]
    exact hga
  obtain ⟨regs', hset', hag'⟩ := setMany_agree hag (hpar ▸ hset)
  refine ⟨_, enterBlock_of (fr := B) (by rw [hB]; exact hBk') hga' (by rw [hpar]; exact hty) hset',
    hA, hB, kInv_set hI (fun x hx => ?_) hset, hsl, hag', hterm, Bk, hBm, List.suffix_refl _, rfl,
    hbody⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact (kOk_spec hk hBm).1 p hp

/-- One statement producing one value. -/
theorem lstep_one {Y : Frame} {m : Mem} {v : ValueId} {i : Inst} {rest : List Stmt} {val : Val}
    (hb : Y.body = ⟨[v], i⟩ :: rest) (hnc : ∀ fn args, i ≠ .call fn args)
    (he : evalInst Y m i = .ok ([val], m)) :
    lstep Y m = .next { Y with regs := Y.regs.set v val, body := rest } m := by
  rw [lstep_inst hb hnc, he]
  rfl

theorem eval_iconst (Y : Frame) (m : Mem) (ty : Ty) (imm : BitVec ty.width) :
    evalInst Y m (.iconst ty imm) = .ok ([⟨ty, imm⟩], m) := rfl

theorem eval_binary {Y : Frame} {m : Mem} {op : BinaryOp} {ty : Ty} {x y : ValueId}
    {a b : BitVec ty.width} (hop : op.isShift = false) (hx : Y.regs x = some ⟨ty, a⟩)
    (hy : Y.regs y = some ⟨ty, b⟩) :
    evalInst Y m (.binary op ty x y) = .ok ([⟨ty, Sem.binary op a b⟩], m) := by
  simp only [evalInst, getAs_of_regs hx, getAs_of_regs hy, hop, Res.ok_bind]
  try rfl

theorem eval_ushr {Y : Frame} {m : Mem} {ty : Ty} {x s : ValueId} {a : BitVec ty.width}
    {vs : Val} (hx : Y.regs x = some ⟨ty, a⟩) (hs : Y.regs s = some vs) :
    evalInst Y m (.binary .ushr ty x s) = .ok ([⟨ty, Sem.ushr a vs.bits⟩], m) := by
  simp only [evalInst, getAs_of_regs hx, Res.ok_bind]
  simp [Frame.get, hs, Res.ofOption, BinaryOp.isShift, Sem.shift]
  try rfl

/-- **A rewritten division**: the source's step is matched by the rewritten statements. -/
theorem div_step {X Y : Frame} {m : Mem} {st : Stmt} {ss yr xs : List Stmt} {s : ValueId}
    {u : Bool} (hw : divRw K s st = some (xs, u)) (hXb : X.body = st :: ss)
    (hYb : Y.body = xs ++ yr) (hI : KInv K X.regs) (hag : Agree (· ∉ S) X.regs Y.regs)
    (hops : ∀ v ∈ operands st.inst, v ∉ S) (hres : ∀ v ∈ st.results, v ∉ S)
    (hsS : u = true → s ∈ S) {X1 : Frame} {m1 : Mem} (hl : lstep X m = .next X1 m1) :
    ∃ Y1, LStar Y m Y1 m1 ∧ X1 = { X with regs := X1.regs, body := ss } ∧
      Y1 = { Y with regs := Y1.regs, body := yr } ∧ Agree (· ∉ S) X1.regs Y1.regs := by
  obtain ⟨v, op, ty, x, y, c, k, rfl, hc, hty, hk, hcase⟩ := divRw_spec hw
  have hnc : ∀ fn args, Inst.div op ty x y ≠ .call fn args := fun _ _ h => by cases h
  rw [lstep_inst hXb hnc] at hl
  cases he : evalInst X m (.div op ty x y) with
  | trap c => rw [he] at hl; cases hl
  | stuck msg => rw [he] at hl; cases hl
  | ok p =>
    obtain ⟨vals, m'⟩ := p
    rw [he] at hl
    simp only [LRes.ofRes] at hl
    cases hs : X.regs.setMany [v] vals with
    | none => simp only [hs] at hl; cases hl
    | some r1 =>
      simp only [hs, LRes.next.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      -- the division's operands and value
      simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok] at he
      obtain ⟨a, ha, b, hb, r, hr, hvals⟩ := he
      simp only [Prod.mk.injEq] at hvals
      obtain ⟨rfl, rfl⟩ := hvals
      have hxa := getAs_regs ha
      have hyb := getAs_regs hb
      have hcb : c = ⟨ty, b⟩ := (hI y c ⟨ty, b⟩ hc hyb).symm
      subst hcb
      simp only at hk
      have hxS : x ∉ S := hops x (by simp [operands])
      have hyS : y ∉ S := hops y (by simp [operands])
      have hvS : v ∉ S := hres v (by simp)
      have hYx : Y.regs x = some ⟨ty, a⟩ := (hag x hxS).trans hxa
      have hYy : Y.regs y = some ⟨ty, b⟩ := (hag y hyS).trans hyb
      have hr1 : r1 = X.regs.set v ⟨ty, r⟩ := by
        simp only [Regs.setMany, Option.some.injEq] at hs
        exact hs.symm
      subst hr1
      -- the agreement after binding `v` to the same value
      have hagree : ∀ (R : Regs), (∀ w, w ∉ S → w ≠ v → R w = Y.regs w) →
          R v = some ⟨ty, r⟩ → Agree (· ∉ S) (X.regs.set v ⟨ty, r⟩) R := by
        intro R hR hRv w hw
        by_cases hwv : w = v
        · subst hwv; rw [hRv]; simp [Regs.set]
        · rw [hR w hw hwv]; simp only [Regs.set, hwv, if_false]; exact hag w hw
      have hw8 := ty_width_ge ty
      have hb0 : b ≠ 0 := bv_ne_zero_of_toNat hk.symm
      have hd := ofExcept_ok hr
      rcases hcase with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, hop, rfl, -⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · -- `urem` by 1: `iconst 0`
        have hb1 : b = 1#ty.width := one_of_toNat (by omega) (by simpa using hk.symm)
        have hr' : r = 0#ty.width := by
          simp only [Sem.div, Sem.urem, if_neg hb0, Except.ok.injEq] at hd
          rw [← hd, hb1, BitVec.umod_one]
        subst hr'
        have hl1 := lstep_one (Y := Y) (m := m) (v := v) (val := ⟨ty, 0#ty.width⟩) hYb
          (fun _ _ h => by cases h) (eval_iconst Y m ty _)
        exact ⟨_, .single hl1, rfl, rfl,
          hagree _ (fun w _ hwv => by simp [Regs.set, hwv]) (by simp [Regs.set])⟩
      · -- `udiv`/`sdiv` by 1: `imul x, y`
        have hb1 : b = 1#ty.width := one_of_toNat (by omega) (by simpa using hk.symm)
        have hra : r = a := by
          rcases hop with rfl | rfl
          · simp only [Sem.div, Sem.udiv, if_neg hb0, Except.ok.injEq] at hd
            rw [← hd, hb1, BitVec.udiv_one]
          · have hne : ¬(a = BitVec.intMin ty.width ∧ b = BitVec.allOnes ty.width) := fun h =>
              bv_one_ne_allOnes (by omega) (hb1 ▸ h.2)
            simp only [Sem.div, Sem.sdiv, if_neg hb0, if_neg hne, Except.ok.injEq] at hd
            rw [← hd, hb1, BitVec.sdiv_one]
        subst hra
        have hev := eval_binary (Y := Y) (m := m) (op := .imul) rfl hYx hYy
        have hval : Sem.binary .imul r b = r := by
          rw [hb1]; simp [Sem.binary, Sem.imul, BitVec.mul_one]
        rw [hval] at hev
        have hl1 := lstep_one (Y := Y) (m := m) (v := v) hYb (fun _ _ h => by cases h) hev
        exact ⟨_, .single hl1, rfl, rfl,
          hagree _ (fun w _ hwv => by simp [Regs.set, hwv]) (by simp [Regs.set])⟩
      · -- `udiv` by `2^k`: `s = iconst k; ushr x, s`
        obtain ⟨hkw, hbk⟩ := twoPow_of_toNat hk.symm
        have hr' : r = Sem.ushr a (BitVec.ofNat ty.width k) := by
          simp only [Sem.div, Sem.udiv, if_neg hb0, Except.ok.injEq] at hd
          rw [← hd, hbk, udiv_pow2 a hkw]
        have hsS' : s ∈ S := hsS rfl
        have hxs : x ≠ s := fun h => hxS (h ▸ hsS')
        have hl1 := lstep_one (Y := Y) (m := m) (v := s) (val := ⟨ty, BitVec.ofNat _ k⟩) hYb
          (fun _ _ h => by cases h) (eval_iconst Y m ty _)
        let Y2 : Frame :=
          { Y with
            regs := Y.regs.set s ⟨ty, BitVec.ofNat _ k⟩
            body := ⟨[v], .binary .ushr ty x s⟩ :: yr }
        have hY2x : Y2.regs x = some ⟨ty, a⟩ := by simp [Y2, Regs.set, hxs, hYx]
        have hY2s : Y2.regs s = some ⟨ty, BitVec.ofNat _ k⟩ := by simp [Y2, Regs.set]
        have hl2 := lstep_one (Y := Y2) (m := m) (v := v) rfl (fun _ _ h => by cases h)
          (eval_ushr hY2x hY2s)
        refine ⟨_, .step hl1 (.single hl2), rfl, rfl, hagree _ (fun w hw hwv => ?_) ?_⟩
        · have hws : w ≠ s := fun h => hw (h ▸ hsS')
          simp [Y2, Regs.set, hwv, hws]
        · simp [Regs.set, hr']
      · -- `urem` by `2^k`: `s = iconst 2^k-1; band x, s`
        obtain ⟨hkw, hbk⟩ := twoPow_of_toNat hk.symm
        have hr' : r = Sem.band a (BitVec.ofNat ty.width (2 ^ k - 1)) := by
          simp only [Sem.div, Sem.urem, if_neg hb0, Except.ok.injEq] at hd
          rw [← hd, hbk, urem_pow2 a hkw]
        have hsS' : s ∈ S := hsS rfl
        have hxs : x ≠ s := fun h => hxS (h ▸ hsS')
        have hl1 := lstep_one (Y := Y) (m := m) (v := s) (val := ⟨ty, BitVec.ofNat _ (2 ^ k - 1)⟩)
          hYb (fun _ _ h => by cases h) (eval_iconst Y m ty _)
        let Y2 : Frame :=
          { Y with
            regs := Y.regs.set s ⟨ty, BitVec.ofNat _ (2 ^ k - 1)⟩
            body := ⟨[v], .binary .band ty x s⟩ :: yr }
        have hY2x : Y2.regs x = some ⟨ty, a⟩ := by simp [Y2, Regs.set, hxs, hYx]
        have hY2s : Y2.regs s = some ⟨ty, BitVec.ofNat _ (2 ^ k - 1)⟩ := by simp [Y2, Regs.set]
        have hl2 := lstep_one (Y := Y2) (m := m) (v := v) rfl (fun _ _ h => by cases h)
          (eval_binary (op := .band) rfl hY2x hY2s)
        refine ⟨_, .step hl1 (.single hl2), rfl, rfl, hagree _ (fun w hw hwv => ?_) ?_⟩
        · have hws : w ≠ s := fun h => hw (h ▸ hsS')
          simp [Y2, Regs.set, hwv, hws]
        · simp [Regs.set, hr', Sem.binary]

/-- A rewritten division never traps, calls or leaves the frame: its divisor is a non-zero
constant. -/
theorem div_only_next {X : Frame} {m : Mem} {st : Stmt} {ss xs : List Stmt} {s : ValueId}
    {u : Bool} (hw : divRw K s st = some (xs, u)) (hXb : X.body = st :: ss) (hI : KInv K X.regs)
    {r : LRes} (hn : ∀ X1 m1, r ≠ .next X1 m1) (hs : ∀ msg, r ≠ .stuck msg) :
    lstep X m ≠ r := by
  intro hl
  obtain ⟨v, op, ty, x, y, c, k, rfl, hc, hty, hk, hcase⟩ := divRw_spec hw
  have hnc : ∀ fn args, Inst.div op ty x y ≠ .call fn args := fun _ _ h => by cases h
  rw [lstep_inst hXb hnc] at hl
  cases he : evalInst X m (.div op ty x y) with
  | ok p =>
    obtain ⟨vals, m'⟩ := p
    rw [he] at hl
    simp only [LRes.ofRes] at hl
    split at hl
    · exact hn _ _ hl.symm
    · exact hs _ hl.symm
  | stuck msg => rw [he] at hl; exact hs msg hl.symm
  | trap tc =>
    simp only [evalInst, Res.bind_eq_trap] at he
    rcases he with h1 | ⟨a, ha, h2⟩
    · exact getAs_ne_trap _ _ _ _ h1
    rcases h2 with h2 | ⟨b, hb, h3⟩
    · exact getAs_ne_trap _ _ _ _ h2
    have hyb := getAs_regs hb
    have hcb : c = ⟨ty, b⟩ := (hI y c ⟨ty, b⟩ hc hyb).symm
    subst hcb
    simp only at hk
    have hb0 : b ≠ 0 := bv_ne_zero_of_toNat hk.symm
    have hw8 := ty_width_ge ty
    have hok : ∃ r, Sem.div op a b = .ok r := by
      rcases hcase with ⟨-, rfl, -⟩ | ⟨hk0, hop, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨a % b, by simp only [Sem.div, Sem.urem, if_neg hb0]⟩
      · subst hk0
        have hb1 : b = 1#ty.width := one_of_toNat (by omega) (by simpa using hk.symm)
        rcases hop with rfl | rfl
        · exact ⟨a / b, by simp only [Sem.div, Sem.udiv, if_neg hb0]⟩
        · have hne : ¬(a = BitVec.intMin ty.width ∧ b = BitVec.allOnes ty.width) := fun h =>
            bv_one_ne_allOnes (by omega) (hb1 ▸ h.2)
          exact ⟨a.sdiv b, by simp only [Sem.div, Sem.sdiv, if_neg hb0, if_neg hne]⟩
      · exact ⟨a / b, by simp only [Sem.div, Sem.udiv, if_neg hb0]⟩
      · exact ⟨a % b, by simp only [Sem.div, Sem.urem, if_neg hb0]⟩
    obtain ⟨r, hr⟩ := hok
    rcases h3 with h3 | ⟨r', -, h4⟩
    · rw [hr] at h3; simp [Res.ofExcept] at h3
    · simp [pure] at h4

/-- A statement step of `f`'s frame keeps `KInv` and moves to the rest of the body. -/
theorem kInv_next (hk : kOk f K = true) {b : Block} (hb : b ∈ f.blocks) {st : Stmt}
    (hst : st ∈ b.body) {X : Frame} {m : Mem} {ss : List Stmt} (hx : X.body = st :: ss)
    (hI : KInv K X.regs) {X1 : Frame} {m1 : Mem} (h : lstep X m = .next X1 m1) :
    KInv K X1.regs ∧ X1 = { X with regs := X1.regs, body := ss } := by
  by_cases hc : ∃ fn args, st.inst = .call fn args
  · obtain ⟨fn, args, hi⟩ := hc
    rw [lstep_call hx hi] at h
    cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h
  · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    rw [lstep_inst hx hnc] at h
    cases he : evalInst X m st.inst with
    | ok p =>
      obtain ⟨vals, m'⟩ := p
      rw [he] at h
      simp only [LRes.ofRes] at h
      cases hs : X.regs.setMany st.results vals with
      | none => simp only [hs] at h; cases h
      | some r1 =>
        simp only [hs, LRes.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨kInv_stmt hk hb hst hI he hs, rfl⟩
    | trap c => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h

/-- A statement step of both frames. -/
theorem DR.stepA (hk : kOk f K = true) (hS : SupOk f S) {X Y : Frame} {m : Mem}
    (h : DR f K bs S X Y) {st : Stmt} {ss : List Stmt} (hx : X.body = st :: ss) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, LStar Y m Y1 m1 ∧ DR f K bs S X1 Y1) ∧
    (∀ ext vals rs rest, lstep X m = .call ext vals rs rest → ∃ rest',
      lstep Y m = .call ext vals rs rest' ∧
      Cont (DR f K bs S) { X with body := rest } rs { Y with body := rest' } rs
        (AbiParam.tys ext.sig.returns)) ∧
    (∀ c, lstep X m = .trap c → lstep Y m = .trap c) := by
  obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := h
  have hst : st ∈ b.body := hsuf.subset (by rw [hx]; simp)
  have hsuf' : ss <:+ b.body := (List.suffix_cons st ss).trans (hx ▸ hsuf)
  obtain ⟨-, hbody, -⟩ := mem_usedVals (f := f) hb
  have hops : ∀ v ∈ operands st.inst, v ∉ S := fun v hv =>
    notS_of_used hS ((hbody st hst).2 v hv)
  have hres : ∀ v ∈ st.results, v ∉ S := fun v hv => notS_of_used hS ((hbody st hst).1 v hv)
  rw [hx] at hbr
  rcases bodyRel_cons hbr with ⟨yr, hyb, hrel⟩ | ⟨s, xs, u, yr, hw, hsS, hyb, hrel⟩
  · -- the same statement
    by_cases hc : ∃ fn args, st.inst = .call fn args
    · obtain ⟨fn, args, hi⟩ := hc
      have hca : callArgs Y fn args = callArgs X fn args := by
        unfold callArgs
        rw [getMany_congr (fr := X) (fr' := Y)
          (fun v hv => hag v (hops v (by simp [hi, operands, hv])))]
        simp only [Function.extern?, hXf, hYf, divFn_externs]
      rw [lstep_call hx hi, lstep_call hyb hi, hca]
      refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
      · cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h
      · cases hcx : callArgs X fn args with
        | ok p =>
          obtain ⟨ext', vals'⟩ := p
          simp only [hcx, LRes.ofRes, LRes.call.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨yr, by simp only [hcx, LRes.ofRes], fun vs regs _ hs => ?_⟩
          obtain ⟨regs', hs', hag'⟩ := setMany_agree hag hs
          exact ⟨regs', hs', hXf, hYf, kInv_set hI (kOk_none hk hb hst (by rw [hi]; rfl)) hs,
            hsl, hag', hYt, b, hb, hsuf', hterm, hrel⟩
        | trap c => simp [hcx, LRes.ofRes] at h
        | stuck msg => simp [hcx, LRes.ofRes] at h
      · cases hcx : callArgs X fn args with
        | ok p => simp [hcx, LRes.ofRes] at h
        | trap c' => simp only [hcx, LRes.ofRes] at h ⊢; exact h
        | stuck msg => simp [hcx, LRes.ofRes] at h
    · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
      have hev : evalInst Y m st.inst = evalInst X m st.inst :=
        evalInst_congr (by rw [hYf, hXf]; rfl) (by rw [hYf, hXf]; rfl) hsl
          (fun x hx => hag x (hops x hx))
      have hlX := lstep_inst (mem := m) hx hnc
      have hlY := lstep_inst (mem := m) hyb hnc
      rw [hev] at hlY
      refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
      · rw [hlX] at h
        cases he : evalInst X m st.inst with
        | ok p =>
          obtain ⟨vals, m'⟩ := p
          rw [he] at h hlY
          simp only [LRes.ofRes] at h hlY
          cases hs : X.regs.setMany st.results vals with
          | none => simp only [hs] at h; cases h
          | some r1 =>
            simp only [hs, LRes.next.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨r1', hs', hag'⟩ := setMany_agree hag hs
            simp only [hs'] at hlY
            exact ⟨_, .single hlY, hXf, hYf, kInv_stmt hk hb hst hI he hs, hsl, hag', hYt, b, hb,
              hsuf', hterm, hrel⟩
        | trap c => rw [he] at h; cases h
        | stuck msg => rw [he] at h; cases h
      · rw [hlX] at h
        cases he : evalInst X m st.inst with
        | ok p =>
          obtain ⟨vals, m'⟩ := p
          rw [he] at h; simp only [LRes.ofRes] at h
          split at h <;> cases h
        | trap c => rw [he] at h; cases h
        | stuck msg => rw [he] at h; cases h
      · rw [hlX] at h
        rw [hlY]
        cases he : evalInst X m st.inst with
        | ok p =>
          obtain ⟨vals, m'⟩ := p
          rw [he] at h; simp only [LRes.ofRes] at h
          split at h <;> cases h
        | trap c' => rw [he] at h; simp only [LRes.ofRes] at h ⊢; exact h
        | stuck msg => rw [he] at h; cases h
  · -- a rewritten division
    refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
    · obtain ⟨Y1, hstar, hX1, hY1, hag1⟩ := div_step hw hx hyb hI hag hops hres hsS h
      obtain ⟨hI1, -⟩ := kInv_next hk hb hst hx hI h
      refine ⟨Y1, hstar, ?_⟩
      rw [hX1, hY1]
      exact ⟨hXf, hYf, hI1, hsl, hag1, hYt, b, hb, hsuf', hterm, hrel⟩
    · exact absurd h (div_only_next hw hx hI (fun _ _ h => by cases h) (fun _ h => by cases h))
    · exact absurd h (div_only_next hw hx hI (fun _ _ h => by cases h) (fun _ h => by cases h))

/-- Both frames at their terminators. -/
theorem DR.stepC (hk : kOk f K = true) (hS : SupOk f S) {X Y : Frame} {m : Mem}
    (h : DR f K bs S X Y) (hx : X.body = []) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ DR f K bs S X1 Y1) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep X m = r →
      lstep Y m = r) := by
  obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := h
  rw [hx] at hbr
  have hy : Y.body = [] := bodyRel_nil hbr
  obtain ⟨-, -, hto⟩ := mem_usedVals (f := f) hb
  have hops : ∀ v ∈ termOperands X.term, v ∉ S := fun v hv =>
    notS_of_used hS (hto v (hterm ▸ hv))
  have henter : ∀ (bc : BlockCall), (∀ a ∈ bc.args, a ∉ S) → ∀ X1 m1,
      LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) = .next X1 m1 →
      ∃ Y1, LRes.ofRes (enterBlock Y bc) (fun fr => LRes.next fr m) = .next Y1 m1 ∧
        DR f K bs S X1 Y1 := by
    intro bc hbc X1 m1 he
    obtain ⟨he1, hm⟩ := ofRes_enter_next he
    subst hm
    obtain ⟨Y1, he', hr⟩ := DR.enter hk hS hXf hYf hI hsl hag hbc he1
    exact ⟨Y1, by rw [he']; rfl, hr⟩
  have hget : ∀ v ∈ termOperands X.term, Y.get v = X.get v := fun v hv => by
    simp only [Frame.get, hag v (hops v hv)]
  rw [lstep_term hx, lstep_term hy, hYt]
  cases hT : X.term with
  | jump d =>
    rw [hT] at hops
    exact ⟨fun X1 m1 h => henter d hops X1 m1 h, fun r hn hs h => absurd h (ofRes_enter_ne hn hs)⟩
  | brif c t e =>
    rw [hT] at hops hget
    simp only
    rw [hget c (by simp [termOperands])]
    have hargs : ∀ cv : Val, ∀ v ∈ (if Sem.truthy cv.bits then t else e).args, v ∉ S :=
      fun cv v hv => hops v (by
        simp only [termOperands, List.mem_cons, List.mem_append]
        split at hv <;> simp [hv])
    refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
    · cases hcv : X.get c with
      | ok cv => rw [hcv] at h; exact henter _ (hargs cv) X1 m1 h
      | trap _ => rw [hcv] at h; cases h
      | stuck _ => rw [hcv] at h; cases h
    · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
  | brTable xi d tbl =>
    rw [hT] at hops hget
    simp only
    rw [hget xi (by simp [termOperands])]
    have hargs : ∀ xv : Val, ∀ v ∈ (tbl[xv.toNat]?.getD d).args, v ∉ S :=
      fun xv v hv => hops v (by
        simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
        cases hq : tbl[xv.toNat]? with
        | none => rw [hq] at hv; exact .inl (.inr hv)
        | some q => rw [hq] at hv; exact .inr ⟨q, List.mem_of_getElem? hq, hv⟩)
    refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
    · cases hxv : X.get xi with
      | ok xv => rw [hxv] at h; exact henter _ (hargs xv) X1 m1 h
      | trap _ => rw [hxv] at h; cases h
      | stuck _ => rw [hxv] at h; cases h
    · exact absurd h (ofRes_get_ne (fun cv => ofRes_enter_ne hn hs) hs)
  | ret xs =>
    rw [hT] at hops
    have hgm : Y.getMany xs = X.getMany xs :=
      getMany_congr (fun v hv => hag v (hops v hv))
    simp only [hgm]
    refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
    cases hg : X.getMany xs <;> rw [hg] at h <;> cases h
  | returnCall fn args =>
    rw [hT] at hops
    have hta : tailArgs Y fn args = tailArgs X fn args := by
      unfold tailArgs
      rw [getMany_congr (fr := X) (fr' := Y) (xs := args) (fun v hv => hag v (hops v hv))]
      simp only [Function.extern?, hXf, hYf, divFn_externs, divFn_sig]
    simp only [hta]
    refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
    cases hg : tailArgs X fn args <;> rw [hg] at h <;> cases h
  | trap tc => exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
  | tryCall fn args et =>
    exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
  | tryCallIndirect c args et =>
    exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩

theorem Pw2.left_mem {α β : Type} {Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pw2 Q xs ys) : ∀ a ∈ xs, ∃ b, Q a b := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hq _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, hq⟩
    · exact ih a ha'

/-- **The frame relation is a simulation with handler edges.** -/
theorem DR.isSimU (hk : kOk f K = true) (hK : ∀ x v, K x = some v → x < f.freshValue)
    (hS : SupOk f S) (hfv : (divFn f K bs S).freshValue = f.freshValue)
    (syms : String → Option Nat) : IsSimU syms (DR f K bs S) := by
  have hwin : ∀ (X : Frame) (n : Nat) (regs : Regs) (vs : List Val), KInv K X.regs →
      X.regs.setMany ((List.range n).map (f.freshValue + ·)) vs = some regs → KInv K regs := by
    intro X n regs vs hI hs
    refine kInv_set hI (fun x hx => ?_) hs
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact kNone_window hK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X Y ⟨hXf, hYf, -, hsl, -⟩
    exact ⟨hsl, by rw [hYf, hXf]; rfl⟩
  · rintro X Y m X1 m1 hr hm hl
    cases hx : X.body with
    | cons st rest => exact (DR.stepA hk hS hr hx (m := m)).1 X1 m1 hl
    | nil =>
      obtain ⟨Y1, h1, h2⟩ := (DR.stepC hk hS hr hx (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
  · rintro X Y m ext vals rs rest hr hm hl
    obtain ⟨st, fn, args, hbd, -⟩ := lstep_call_inv hl
    obtain ⟨rest', h1, h2⟩ := (DR.stepA hk hS hr hbd (m := m)).2.1 ext vals rs rest hl
    exact ⟨Y, rs, rest', .refl _ _, h1, h2⟩
  · rintro X Y m vals hr hm hl
    exact ⟨Y, .refl _ _, (DR.stepC hk hS hr (lstep_ret_inv hl) (m := m)).2 _
      (fun _ _ h => by cases h) (fun _ h => by cases h) hl⟩
  · rintro X Y m ext vals hr hm hl
    exact ⟨Y, .refl _ _, (DR.stepC hk hS hr (lstep_tail_inv hl) (m := m)).2 _
      (fun _ _ h => by cases h) (fun _ h => by cases h) hl⟩
  · rintro X Y m c hr hm hl
    cases hx : X.body with
    | cons st rest => exact ⟨Y, m, .refl _ _, (DR.stepA hk hS hr hx (m := m)).2.2 c hl⟩
    | nil =>
      exact ⟨Y, m, .refl _ _, (DR.stepC hk hS hr hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro X Y m st rest sig callee args d a vals hr hm hbd hi hca
    obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := hr
    have hst : st ∈ b.body := hsuf.subset (by rw [hbd]; simp)
    obtain ⟨-, hbody, -⟩ := mem_usedVals (f := f) hb
    have hops : ∀ v ∈ operands st.inst, v ∉ S := fun v hv =>
      notS_of_used hS ((hbody st hst).2 v hv)
    rw [hbd] at hbr
    rcases bodyRel_cons hbr with ⟨yr, hyb, hrel⟩ | ⟨s, xs, u, yr, hw, -, -, -⟩
    · refine ⟨Y, st, yr, sig, callee, args, .refl _ _, hyb, hi, ?_, ?_⟩
      · rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hops v (by simp [hi, operands, hv])))]
        simp only [Frame.get, hag callee (hops callee (by simp [hi, operands])), hXf, hYf,
          divFn_sigDecls]
      · intro vs regs _ hset
        obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
        exact ⟨regs', hset', hXf, hYf, kInv_set hI (kOk_none hk hb hst (by rw [hi]; rfl)) hset,
          hsl, hag', hYt, b, hb, (List.suffix_cons st rest).trans (hbd ▸ hsuf), hterm, hrel⟩
    · obtain ⟨_, _, _, _, _, _, _, hst', -⟩ := divRw_spec hw
      rw [hst'] at hi; cases hi
  · -- `try_call`, `try_call_indirect`
    have hpost : ∀ (X Y : Frame) (n : Nat) (bc : BlockCall) (et : ExnTable) (rtys : List Ty),
        DR f K bs S X Y → (∀ v ∈ et.vals, v ∉ S) →
        tryNormal et X.func.freshValue = .ok bc →
        TCont (DR f K bs S) X (tryRets n X.func.freshValue) bc Y
          (tryRets n Y.func.freshValue) bc rtys := by
      rintro X Y n bc et rtys ⟨hXf, hYf, hI, hsl, hag, -⟩ hvals hbc vs regs _ hset
      have hfv' : Y.func.freshValue = X.func.freshValue := by rw [hYf, hXf, hfv]
      rw [hfv']
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      refine ⟨regs', hset', fun X1 he => ?_⟩
      have hI' : KInv K regs := hwin X n regs vs hI (by rw [← hXf]; exact hset)
      obtain ⟨bc2, -, -, hpw⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := X.func.freshValue) hbc
      have hargs : ∀ a ∈ bc.args, a ∉ S := by
        intro a ha hs
        have hlt := hS.lt a hs
        obtain ⟨_, hq⟩ := Pw2.left_mem hpw a ha
        rcases hq with ⟨v, hv, rfl, -⟩ | ⟨i, rfl, -⟩
        · exact hvals _ (by simp [ExnTable.vals, hv]) hs
        · rw [hXf] at hlt; exact absurd hlt (Nat.not_lt.2 (Nat.le_add_right _ _))
      exact DR.enter hk hS (A := { X with regs }) (B := { Y with regs := regs' }) hXf hYf hI'
        hsl hag' hargs he
    have hhand : ∀ (X Y : Frame) (et : ExnTable), DR f K bs S X Y → (∀ v ∈ et.vals, v ∉ S) →
        HCont (DR f K bs S) X et Y et := by
      rintro X Y et ⟨hXf, hYf, hI, hsl, hag, -⟩ hvals e
      refine ⟨fun hn => catchIn_eq_none.2 (catchIn_eq_none.1 hn), fun X1 hc => ?_⟩
      obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
      have hfv' : Y.func.freshValue = X.func.freshValue := by rw [hYf, hXf, hfv]
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      have hbc' : tryHandler d Y.func.freshValue = .ok bc := by rw [hfv']; exact hbc
      have hset'' : Y.regs.setMany ((List.range e.payload.length).map (Y.func.freshValue + ·))
          e.payload = some regs' := by rw [hfv']; exact hset'
      refine ⟨_, catchIn_of hd hbc' hset'', rfl, rfl, bc, bc, rfl, rfl, fun X2 he => ?_⟩
      have he0 : enterBlock { X with regs } bc = .ok X2 := by
        rw [← enterBlock_bt { X with regs } [] (.jump bc)]; exact he
      have hI' : KInv K regs := hwin X _ regs _ hI (by rw [← hXf]; exact hset)
      obtain ⟨bc2, -, -, hpw⟩ := tryHandler_pair id (b2 := X.func.freshValue) hbc
      have hdm := catch?_mem hd
      have hargs : ∀ a ∈ bc.args, a ∉ S := by
        intro a ha hs
        have hlt := hS.lt a hs
        obtain ⟨_, hq⟩ := Pw2.left_mem hpw a ha
        rcases hq with ⟨v, hv, rfl, -⟩ | ⟨i, rfl, -⟩
        · exact hvals _ (handler_vals hdm hv) hs
        · rw [hXf] at hlt; exact absurd hlt (Nat.not_lt.2 (Nat.le_add_right _ _))
      obtain ⟨Y2, he', hr⟩ := DR.enter hk hS (A := { X with regs }) (B := { Y with regs := regs' })
        hXf hYf hI' hsl hag' hargs he0
      exact ⟨Y2, (enterBlock_bt { Y with regs := regs' } [] (.jump bc) bc).trans he', hr⟩
    have hvals : ∀ X Y, DR f K bs S X Y → X.body = [] → ∀ t, X.term = t →
        ∀ v ∈ termOperands t, v ∉ S := by
      rintro X Y ⟨-, -, -, -, -, -, b, hb, -, hterm, -⟩ - t ht v hv
      obtain ⟨-, -, hto⟩ := mem_usedVals (f := f) hb
      exact notS_of_used hS (hto v (by rw [← hterm, ht]; exact hv))
    have hyb : ∀ X Y, DR f K bs S X Y → X.body = [] → Y.body = [] ∧ Y.term = X.term := by
      rintro X Y ⟨-, -, -, -, -, hYt, -, -, -, -, hbr⟩ hx
      rw [hx] at hbr
      exact ⟨bodyRel_nil hbr, hYt⟩
    refine ⟨?_, ?_⟩
    · rintro X Y m fn args et n base bc ext vals hr hm hbd ht htc hca
      obtain ⟨hy, hYt⟩ := hyb X Y hr hbd
      have hops := hvals X Y hr hbd _ ht
      have hr0 := hr
      obtain ⟨hXf, hYf, -, hsl, hag, -⟩ := hr
      obtain ⟨rfl, hbc⟩ := tcArgs_base htc
      have htc' : tcArgs Y fn et = tcArgs X fn et := by
        unfold tcArgs
        simp only [Function.extern?, hXf, hYf, divFn_externs, divFn_sigDecls, hfv]
      have hca' : callArgs Y fn args = callArgs X fn args := by
        unfold callArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hops v (by simp [termOperands, hv])))]
        simp only [Function.extern?, hXf, hYf, divFn_externs]
      have hfv' : Y.func.freshValue = X.func.freshValue := by rw [hYf, hXf, hfv]
      refine ⟨Y, fn, args, et, X.func.freshValue, bc, .refl _ _, hy, by rw [hYt, ht],
        by rw [htc']; exact htc, by rw [hca']; exact hca, ?_,
        hhand X Y et hr0 (fun v hv => hops v (by simp [termOperands, hv]))⟩
      have := hpost X Y n bc et (AbiParam.tys ext.sig.returns) hr0
        (fun v hv => hops v (by simp [termOperands, hv])) hbc
      rwa [hfv'] at this
    · rintro X Y m callee args et n base bc d a vals hr hm hbd ht htc hca
      obtain ⟨hy, hYt⟩ := hyb X Y hr hbd
      have hops := hvals X Y hr hbd _ ht
      have hr0 := hr
      obtain ⟨hXf, hYf, -, hsl, hag, -⟩ := hr
      obtain ⟨rfl, hbc⟩ := ticArgs_base htc
      have htc' : ticArgs Y et = ticArgs X et := by
        unfold ticArgs
        simp only [hXf, hYf, divFn_sigDecls, hfv]
      have hca' : ciArgs Y et.sig callee args = ciArgs X et.sig callee args := by
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hops v (by simp [termOperands, hv])))]
        simp only [Frame.get, hag callee (hops callee (by simp [termOperands])), hXf, hYf,
          divFn_sigDecls]
      have hfv' : Y.func.freshValue = X.func.freshValue := by rw [hYf, hXf, hfv]
      refine ⟨Y, callee, args, et, X.func.freshValue, bc, .refl _ _, hy, by rw [hYt, ht],
        by rw [htc']; exact htc, by rw [hca']; exact hca, ?_,
        hhand X Y et hr0 (fun v hv => hops v (by simp [termOperands, hv]))⟩
      have := hpost X Y n bc et (AbiParam.tys d.returns) hr0
        (fun v hv => hops v (by simp [termOperands, hv])) hbc
      rwa [hfv'] at this

/-- **The rewritten function simulates `f`.** -/
theorem divFn_simU (hk : kOk f K = true) (hK : ∀ x v, K x = some v → x < f.freshValue)
    (hS : SupOk f S) (hfv : (divFn f K bs S).freshValue = f.freshValue) :
    FunSimU f (divFn f K bs S) where
  name := rfl
  sig := rfl
  slots := rfl
  externs := rfl
  sim syms := by
    refine ⟨DR f K bs S, DR.isSimU hk hK hS hfv syms, fun b hb => ?_⟩
    obtain ⟨b', hb', hid, hpar, hterm, hbody⟩ :=
      divBlocks_head (K := K) (bs := bs) (S := S) (sup := S) (fun s hs => hs) hb
    refine ⟨b', hb', hpar, fun args regs slots _ hset _ => ?_⟩
    have hbm : b ∈ f.blocks := List.mem_of_mem_head? hb
    refine ⟨rfl, rfl, kInv_set (kInv_empty K) (fun x hx => ?_) hset, rfl, fun _ _ => rfl,
      hterm, b, hbm, List.suffix_refl _, rfl, hbody⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (kOk_spec hk hbm).1 p hp

end

/-- **Division by a constant is simulated by its input.** -/
theorem divPre_simU (f : Function) (bs : List BlockId) : FunSimU f (divPre f bs) := by
  unfold divPre
  split
  · exact FunSimU.refl f
  · dsimp only
    split
    · rename_i hk
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact divFn_simU hk (fun _ _ h => kLook_lt h) (supOk_of hc.1) hc.2
      · exact FunSimU.refl f
    · exact FunSimU.refl f

/-- **The folded function without its unreachable blocks is simulated by its input**
(the validator's constant-phi removal `phiPre`, divisions by constants rewritten, branches
folded, constant-phi removal). -/
theorem foldPre_simU (f : Function) (bs : List BlockId) : FunSimU f (foldPre f bs) :=
  (phiPre_simU f).trans ((divPre_simU _ bs).trans ((foldBr_simU _ bs).trans (ConstPhi.run_simU _)))

end Opt.MidVal
