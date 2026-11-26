import FV.Opt.Proof.MidValDiv
import FV.Opt.Proof.RuleInfraDivConst
import FV.Opt.Proof.RuleSkeleton5

/-!
# Division by a constant with magic numbers is simulated by its input (#1119)

Cranelift's mid-end (0.136.1, `opts/arithmetic.isle`, `prelude_opt.isle`, `opts/div_const.rs`;
0.135.0, the version cg_clif links and the corpus dumps come from, has the same text in
`div_const.rs`, in the division rules of `arithmetic.isle` and in `prelude_opt.isle`'s
`apply_div_const_magic_*`, so the sequences are the same) replaces an unsigned division or
remainder by a constant `d` that is neither 0, 1 nor a power of two, at width 32 or 64, with a
multiply-high and shifts (Granlund–Montgomery, Hacker's Delight 10-8), and a signed one whose
`|d|` is neither 0, 1 nor a power of two with a signed multiply-high, a sign correction and
shifts. `Opt.MidVal.magicPre f bs` (`FV/Opt/MidValFold.lean`) does the
same to `f`'s `udiv`/`urem`/`sdiv`/`srem` whose divisor has a constant in
`K = kLook f.freshValue (kTable f)` (checked by `kOk`), in the blocks `bs`, with Cranelift's magic
numbers (`Isle.Opt.Rust.magicU`/`magicS`, the ports of `magic_u32`/`magic_u64`/`magic_s32`/
`magic_s64` the ISLE interpreter runs); the new values are numbered from `f.freshValue` on (`f`
reads only values below it, `refsOk`); `skeleton-removed div`. Here:
**`magicPre_simU : FunSimU f (magicPre f bs)`**, and **`foldPre_simU`** / **`foldPreK_simU`** for
the whole preparation (`foldPre f bs = ConstPhi.run (foldBr (magicPre (divPre (phiPre f) bs) bs)
bs)`; `divPre_simU`: `FV/Opt/Proof/MidValDiv.lean`).

* The arithmetic is the ISLE rules' (`FV/Opt/Proof/RuleInfraDivConst.lean`): `magicU_spec`
  (`Isle.Opt.Rust.magicU`'s numbers compute the quotient of every `x < 2^w`), as `MagicFactsU`
  (`magicU_facts`), and the bit-vector forms `udiv_magic_noadd`/`udiv_magic_add`/`urem_of_udiv`;
  here the four sequences of `uQuot` in the validator's operations (`magic_noadd0`, `magic_noadd`,
  `magic_add1`, `magic_add`) and the remainder (`urem_of_quot`).
* The statements: `uQuot_run`/`magicStmts_run` (`RunS`, `FV/Opt/Proof/MidValCondSim.lean`) put the
  division's value in its result and write only values from `n` on; `RunS.lstar` makes them
  steps of the rewritten frame.
* The frame relation `MagR`: the same point of a block of `f`, the rewritten frame running the
  rewritten rest of that block's body (`BodyRelM`), registers agreeing below `f.freshValue`, the
  same slots and terminator, and `KInv` in `f`'s frame. The rewritten function's fresh value is at
  least `f`'s (`magicFn_freshValue_ge`), so a `try_call`'s results and a handler's payload (bound
  at each side's fresh value, equal windows: `IsSimWU`, `FV/Opt/Proof/SimWinU.lean`) keep the
  agreement, as for `condPrep` (`CR.isSimWU`).
-/

namespace Opt.MidVal

open Clif

/-! ## The arithmetic -/

theorem sem_ushr_ofNat {w s : Nat} (a : BitVec w) (hs : s < w) :
    Sem.ushr a (BitVec.ofNat w s) = a >>> s := by
  unfold Sem.ushr Sem.shiftAmt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs Nat.lt_two_pow_self),
    Nat.mod_eq_of_lt hs]

theorem log2Exact_none {n : Nat} (h : log2Exact n = none) : ∀ k, n ≠ 2 ^ k := by
  intro k hk
  subst hk
  simp [log2Exact, Nat.log2_two_pow] at h

/-- The facts of Cranelift's unsigned magic numbers the rewrite relies on
(`Opt.Proof.DivConst.magicU_spec`): `M < 2^w`, and the quotient of every `x < 2^w` by the
multiply-high and the shift (without the add step), or by the add step and the shift `s - 1`. -/
def MagicFactsU (w d M : Nat) (add : Bool) (s : Nat) : Prop :=
  M < 2 ^ w ∧ ((add = false ∧ s < w ∧ ∀ x < 2 ^ w, x * M / 2 ^ w / 2 ^ s = x / d) ∨
    (add = true ∧ 1 ≤ s ∧ s ≤ w ∧
      ∀ x < 2 ^ w, ((x - x * M / 2 ^ w) / 2 + x * M / 2 ^ w) / 2 ^ (s - 1) = x / d))

/-- `Isle.Opt.Rust.magicU`'s numbers have the facts, for every divisor `2 ≤ d < 2^w` that is not a
power of two. -/
theorem magicU_facts {w d : Nat} (hw : 1 ≤ w) (hd : 2 ≤ d) (hdw : d < 2 ^ w)
    (hpow : ∀ k, d ≠ 2 ^ k) :
    MagicFactsU w d (Isle.Opt.Rust.magicU w d).1 (Isle.Opt.Rust.magicU w d).2.1
      (Isle.Opt.Rust.magicU w d).2.2.toNat := by
  obtain ⟨m, s, hm, h⟩ := Opt.Proof.DivConst.magicU_spec hw hd hdw hpow
  rcases h with ⟨he, hs, hq⟩ | ⟨he, hs1, hs2, hq⟩
  · rw [he]; exact ⟨hm, .inl ⟨rfl, by simpa using hs, by simpa using hq⟩⟩
  · rw [he]; exact ⟨hm, .inr ⟨rfl, by simpa using hs1, by simpa using hs2, by simpa using hq⟩⟩

/-- **The sequence without the add step and shift 0**: the high half alone. -/
theorem magic_noadd0 {w d M : Nat} (h : MagicFactsU w d M false 0) (a b : BitVec w)
    (hb : b.toNat = d := by rfl) :
    Sem.binary .umulhi a (BitVec.ofNat w M) = a / b := by
  obtain ⟨hM, hq⟩ := h
  rcases hq with ⟨-, -, hq⟩ | ⟨h, -⟩
  · have := Opt.Proof.DivConst.udiv_magic_noadd a b M 0 hM (by rw [hb]; exact hq)
    rwa [BitVec.ushiftRight_zero] at this
  · cases h

/-- **The sequence without the add step.** -/
theorem magic_noadd {w d M s : Nat} (h : MagicFactsU w d M false s) (a b : BitVec w)
    (hb : b.toNat = d := by rfl) :
    Sem.ushr (Sem.binary .umulhi a (BitVec.ofNat w M)) (BitVec.ofNat w s) = a / b := by
  obtain ⟨hM, hq⟩ := h
  rcases hq with ⟨-, hs, hq⟩ | ⟨h, -⟩
  · rw [sem_ushr_ofNat _ hs]
    exact Opt.Proof.DivConst.udiv_magic_noadd a b M s hM (by rw [hb]; exact hq)
  · cases h

/-- **The sequence with the add step and a final shift by `s - 1 = 0`** (left out). -/
theorem magic_add1 {w d M s : Nat} (h : MagicFactsU w d M true s) (a b : BitVec w) (hw : 1 < w)
    (hs : s ≤ 1) (hb : b.toNat = d := by rfl) :
    Sem.binary .iadd (Sem.binary .umulhi a (BitVec.ofNat w M))
      (Sem.ushr (Sem.binary .isub a (Sem.binary .umulhi a (BitVec.ofNat w M))) (BitVec.ofNat w 1)) =
      a / b := by
  obtain ⟨hM, hq⟩ := h
  rcases hq with ⟨h, -⟩ | ⟨-, hs1, -, hq⟩
  · cases h
  · have hs' : s = 1 := by omega
    subst hs'
    have := Opt.Proof.DivConst.udiv_magic_add a b M 1 hM (by rw [hb]; exact hq)
    rw [Nat.sub_self, BitVec.ushiftRight_zero] at this
    show Sem.iadd _ (Sem.ushr (Sem.isub _ _) _) = _
    unfold Sem.iadd Sem.isub
    rw [sem_ushr_ofNat _ hw, BitVec.add_comm]
    exact this

/-- **The sequence with the add step and a final shift by `s - 1 ≥ 1`.** -/
theorem magic_add {w d M s : Nat} (h : MagicFactsU w d M true s) (a b : BitVec w) (hw : 1 < w)
    (hs : 2 ≤ s) (hb : b.toNat = d := by rfl) :
    Sem.ushr (Sem.binary .iadd (Sem.binary .umulhi a (BitVec.ofNat w M))
      (Sem.ushr (Sem.binary .isub a (Sem.binary .umulhi a (BitVec.ofNat w M))) (BitVec.ofNat w 1)))
      (BitVec.ofNat w (s - 1)) = a / b := by
  obtain ⟨hM, hq⟩ := h
  rcases hq with ⟨h, -⟩ | ⟨-, -, hs2, hq⟩
  · cases h
  · have := Opt.Proof.DivConst.udiv_magic_add a b M s hM (by rw [hb]; exact hq)
    show Sem.ushr (Sem.iadd _ (Sem.ushr (Sem.isub _ _) _)) _ = _
    unfold Sem.iadd Sem.isub
    rw [sem_ushr_ofNat _ hw, sem_ushr_ofNat _ (by omega), BitVec.add_comm]
    exact this

/-- The remainder from the quotient: `a - (a/b)·b = a % b`. -/
theorem urem_of_quot {w : Nat} (a b : BitVec w) :
    Sem.binary .isub a (Sem.binary .imul (a / b) b) = a % b :=
  Opt.Proof.DivConst.urem_of_udiv a b

/-! ## Running straight-line statements -/

/-- `RunS` forwards: one run, then the next. -/
theorem RunS.app {T : Frame} {r r1 r2 : Regs} {ss ss' : List Stmt} (h1 : RunS T r ss r1)
    (h2 : RunS T r1 ss' r2) : RunS T r (ss ++ ss') r2 := by
  induction h1 with
  | nil => exact h2
  | cons he hs _ ih => exact .cons he hs (ih h2)

theorem RunS.iconst {T : Frame} {r r2 : Regs} {v : ValueId} {ty : Ty} {imm : BitVec ty.width}
    {ss : List Stmt} (h : RunS T (r.set v ⟨ty, imm⟩) ss r2) :
    RunS T r (⟨[v], .iconst ty imm⟩ :: ss) r2 :=
  .cons (fun _ => rfl) rfl h

theorem RunS.bin {T : Frame} {r r2 : Regs} {v x y : ValueId} {op : BinaryOp} {ty : Ty}
    {a c : BitVec ty.width} {ss : List Stmt} (hop : op.isShift = false)
    (hx : r x = some ⟨ty, a⟩) (hy : r y = some ⟨ty, c⟩)
    (h : RunS T (r.set v ⟨ty, Sem.binary op a c⟩) ss r2) :
    RunS T r (⟨[v], .binary op ty x y⟩ :: ss) r2 :=
  .cons (fun _ => eval_binary (Y := { T with regs := r }) hop hx hy) rfl h

theorem RunS.ushr {T : Frame} {r r2 : Regs} {v x y : ValueId} {ty : Ty} {a : BitVec ty.width}
    {vs : Val} {ss : List Stmt} (hx : r x = some ⟨ty, a⟩) (hy : r y = some vs)
    (h : RunS T (r.set v ⟨ty, Sem.ushr a vs.bits⟩) ss r2) :
    RunS T r (⟨[v], .binary .ushr ty x y⟩ :: ss) r2 :=
  .cons (fun _ => eval_ushr (Y := { T with regs := r }) hx hy) rfl h

/-- Statements that run from `r` to `r2` are `LStar` steps of a frame like `Y`. -/
theorem RunS.lstar {Y : Frame} {r r2 : Regs} {ss : List Stmt} (h : RunS Y r ss r2)
    (hnc : ∀ st ∈ ss, ∀ fn args, st.inst ≠ .call fn args) (yr : List Stmt) (m : Mem) :
    LStar { Y with regs := r, body := ss ++ yr } m { Y with regs := r2, body := yr } m := by
  induction h with
  | nil r => exact .refl _ _
  | @cons r r1 r2 st ss vals he hs _ ih =>
    have hnc1 : ∀ fn args, st.inst ≠ .call fn args := hnc st (List.mem_cons_self ..)
    have hl : lstep { Y with regs := r, body := st :: ss ++ yr } m =
        .next { Y with regs := r1, body := ss ++ yr } m := by
      rw [lstep_inst (rest := ss ++ yr) rfl hnc1,
        (evalInst_congr (fr := { Y with regs := r })
          (fr' := { Y with regs := r, body := st :: ss ++ yr })
          rfl rfl rfl (fun _ _ => rfl)).trans (he m)]
      simp only [LRes.ofRes, hs]
    exact .step hl (ih (fun st h => hnc st (List.mem_cons_of_mem _ h)))

/-! ## The rewritten statements -/

theorem uQuot_noCall (ty : Ty) (x : ValueId) (M : Nat) (add : Bool) (s n dst : ValueId) :
    ∀ st ∈ (uQuot ty x M add s n dst).1, ∀ fn args, st.inst ≠ .call fn args := by
  unfold uQuot
  split <;> (try split) <;> simp

/-- The high half of `a·M` (`umulhi a, M`), and the add step's halved difference
`(a - umulhi a, M) >> 1`: names for the values of `uQuot`'s statements. -/
abbrev hiU {w : Nat} (a : BitVec w) (M : Nat) : BitVec w := Sem.binary .umulhi a (BitVec.ofNat w M)

@[inherit_doc hiU]
abbrev halfU {w : Nat} (a : BitVec w) (M : Nat) : BitVec w :=
  Sem.ushr (Sem.binary .isub a (hiU a M)) (BitVec.ofNat w 1)

/-- **The unsigned quotient by the magic numbers runs** to `a / b` in `dst`, its temporaries
(from `n` on) the only other registers written. -/
theorem uQuot_run (T : Frame) {r : Regs} {ty : Ty} {x : Nat} {a b : BitVec ty.width}
    {M : Nat} {add : Bool} {s n dst : Nat} (hx : r x = some ⟨ty, a⟩) (hxn : x < n)
    (hf : MagicFactsU ty.width b.toNat M add s) :
    ∃ r2, RunS T r (uQuot ty x M add s n dst).1 r2 ∧ r2 dst = some ⟨ty, a / b⟩ ∧
      ∀ w, w < n → w ≠ dst → r2 w = r w := by
  have hx0 : x ≠ n := by omega
  have hx1 : x ≠ n + 1 := by omega
  have hx2 : x ≠ n + 2 := by omega
  have hx3 : x ≠ n + 3 := by omega
  have hx4 : x ≠ n + 4 := by omega
  have hw8 := ty_width_ge ty
  unfold uQuot
  cases add with
  | true =>
    simp only [ite_true]
    split
    · rename_i hs
      have hv := magic_add1 hf a b (by omega) hs
      refine ⟨_, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofNat ty.width M) rfl ?_ ?_
        (RunS.bin (a := a) (c := hiU a M) rfl ?_ ?_ (RunS.iconst
        (RunS.ushr (a := Sem.binary .isub a (hiU a M)) (vs := ⟨ty, BitVec.ofNat ty.width 1⟩) ?_ ?_
        (RunS.bin (a := hiU a M) (c := halfU a M) rfl ?_ ?_ (.nil _)))))), ?_, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · simp [Regs.set, hx0, hx1, hx]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp only [Regs.set_same]; exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) hv
      · intro w hw hwd
        have h0 : w ≠ n := by omega
        have h1 : w ≠ n + 1 := by omega
        have h2 : w ≠ n + 2 := by omega
        have h3 : w ≠ n + 3 := by omega
        have h4 : w ≠ n + 4 := by omega
        simp [Regs.set, hwd, h0, h1, h2, h3, h4]
    · rename_i hs
      have hv := magic_add hf a b (by omega) (by omega)
      refine ⟨_, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofNat ty.width M) rfl ?_ ?_
        (RunS.bin (a := a) (c := hiU a M) rfl ?_ ?_ (RunS.iconst
        (RunS.ushr (a := Sem.binary .isub a (hiU a M)) (vs := ⟨ty, BitVec.ofNat ty.width 1⟩) ?_ ?_
        (RunS.bin (a := hiU a M) (c := halfU a M) rfl ?_ ?_ (RunS.iconst
        (RunS.ushr (a := Sem.binary .iadd (hiU a M) (halfU a M))
          (vs := ⟨ty, BitVec.ofNat ty.width (s - 1)⟩) ?_ ?_ (.nil _)))))))), ?_, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · simp [Regs.set, hx0, hx1, hx]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp only [Regs.set_same]; exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) hv
      · intro w hw hwd
        have h0 : w ≠ n := by omega
        have h1 : w ≠ n + 1 := by omega
        have h2 : w ≠ n + 2 := by omega
        have h3 : w ≠ n + 3 := by omega
        have h4 : w ≠ n + 4 := by omega
        have h5 : w ≠ n + 5 := by omega
        have h6 : w ≠ n + 6 := by omega
        simp [Regs.set, hwd, h0, h1, h2, h3, h4, h5, h6]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    split
    · rename_i hs
      subst hs
      have hv := magic_noadd0 hf a b
      refine ⟨_, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofNat ty.width M) rfl ?_ ?_ (.nil _)),
        ?_, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · simp only [Regs.set_same]; exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) hv
      · intro w hw hwd
        have h0 : w ≠ n := by omega
        simp [Regs.set, hwd, h0]
    · have hv := magic_noadd hf a b
      refine ⟨_, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofNat ty.width M) rfl ?_ ?_
        (RunS.iconst
        (RunS.ushr (a := hiU a M) (vs := ⟨ty, BitVec.ofNat ty.width s⟩) ?_ ?_ (.nil _)))), ?_, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp only [Regs.set_same]; exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) hv
      · intro w hw hwd
        have h0 : w ≠ n := by omega
        have h1 : w ≠ n + 1 := by omega
        have h2 : w ≠ n + 2 := by omega
        simp [Regs.set, hwd, h0, h1, h2]

/-- The statements of a division by magic numbers: none is a call. -/
theorem magicStmts_noCall (op : DivOp) (ty : Ty) (v x y : ValueId) (M : Nat) (add : Bool)
    (s n : Nat) :
    ∀ st ∈ (magicStmts op ty v x y M add s n).1, ∀ fn args, st.inst ≠ .call fn args := by
  intro st hst fn args h
  unfold magicStmts at hst
  split at hst
  · exact uQuot_noCall ty x M add s n v st hst fn args h
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with hst | hst | hst
    · exact uQuot_noCall ty x M add s (n + 1) n st hst fn args h
    · subst hst; cases h
    · subst hst; cases h

/-- **The statements of a division by magic numbers run** to the division's value in `v`, the
values from `n` on the only other registers written. -/
theorem magicStmts_run (T : Frame) {r : Regs} {op : DivOp} {ty : Ty} {v x y : Nat}
    {a b : BitVec ty.width} {M : Nat} {add : Bool} {s n : Nat} (hop : op = .udiv ∨ op = .urem)
    (hx : r x = some ⟨ty, a⟩) (hy : r y = some ⟨ty, b⟩) (hxn : x < n) (hyn : y < n)
    (hd2 : 2 ≤ b.toNat) (hf : MagicFactsU ty.width b.toNat M add s) {res : BitVec ty.width}
    (hres : Sem.div op a b = .ok res) :
    ∃ r2, RunS T r (magicStmts op ty v x y M add s n).1 r2 ∧ r2 v = some ⟨ty, res⟩ ∧
      ∀ w, w < n → w ≠ v → r2 w = r w := by
  have hb0 : b ≠ 0 := by intro h; rw [h] at hd2; simp at hd2
  unfold magicStmts
  cases op <;> simp only [reduceCtorEq, or_self, or_false, false_or] at hop
  · simp only [ite_true]
    have hr : res = a / b := by
      simp only [Sem.div, Sem.udiv, if_neg hb0, Except.ok.injEq] at hres; exact hres.symm
    subst hr
    exact uQuot_run T hx hxn hf
  · simp only [reduceCtorEq, ite_false]
    have hr : res = a % b := by
      simp only [Sem.div, Sem.urem, if_neg hb0, Except.ok.injEq] at hres; exact hres.symm
    subst hr
    obtain ⟨r1, h1, hq, hfr⟩ := uQuot_run T (n := n + 1) (dst := n) hx (by omega) hf
    have hx1 : r1 x = some ⟨ty, a⟩ := by rw [hfr x (by omega) (by omega), hx]
    have hy1 : r1 y = some ⟨ty, b⟩ := by rw [hfr y (by omega) (by omega), hy]
    generalize hk : (uQuot ty x M add s (n + 1) n).2 = k
    have hxk : x ≠ n + 1 + k := by omega
    refine ⟨_, h1.app (RunS.bin rfl hq hy1
      (RunS.bin (a := a) (c := Sem.binary .imul (a / b) b) rfl ?_ ?_
      (.nil _))), ?_, ?_⟩
    · simp [Regs.set, hxk, hx1]
    · simp [Regs.set]
    · simp only [Regs.set_same]
      exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) (urem_of_quot a b)
    · intro w hw hwv
      have h0 : w ≠ n + 1 + k := by omega
      simp only [Regs.set, hwv, h0, if_false]
      exact hfr w (by omega) (by omega)

theorem uQuot_mem_dst (ty : Ty) (x : ValueId) (M : Nat) (add : Bool) (s n dst : ValueId) :
    ∃ st ∈ (uQuot ty x M add s n dst).1, dst ∈ st.results := by
  unfold uQuot
  split
  · split
    · exact ⟨⟨[dst], .binary .iadd ty (n + 1) (n + 4)⟩, by simp, by simp⟩
    · exact ⟨⟨[dst], .binary .ushr ty (n + 5) (n + 6)⟩, by simp, by simp⟩
  · split
    · exact ⟨⟨[dst], .binary .umulhi ty x n⟩, by simp, by simp⟩
    · exact ⟨⟨[dst], .binary .ushr ty (n + 1) (n + 2)⟩, by simp, by simp⟩

theorem magicStmts_mem_v (op : DivOp) (ty : Ty) (v x y : ValueId) (M : Nat) (add : Bool)
    (s n : Nat) : ∃ st ∈ (magicStmts op ty v x y M add s n).1, v ∈ st.results := by
  unfold magicStmts
  split
  · exact uQuot_mem_dst ty x M add s n v
  · exact ⟨⟨[v], .binary .isub ty x (n + 1 + (uQuot ty x M add s (n + 1) n).2)⟩, by simp, by simp⟩

/-! ## The signed sequence -/

/-- The signed sequence's `q2` (`Opt.Proof.DivConst.magicS_spec`): the high half of `x·m`, with
the fix-up. -/
abbrev qS (w : Nat) (d m x : Int) : Int :=
  if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
  else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w

/-- The facts of Cranelift's signed magic numbers the rewrite relies on
(`Opt.Proof.DivConst.magicS_spec`): `m` a signed `w`-bit value, `s < w`, and for every signed
`w`-bit `x` the fix-up `qS` stays in range and the shift and sign correction give `x.tdiv d`. -/
def MagicFactsS (w : Nat) (d m : Int) (s : Nat) : Prop :=
  -2 ^ (w - 1) ≤ m ∧ m < 2 ^ (w - 1) ∧ s < w ∧
    ∀ x : Int, -2 ^ (w - 1) ≤ x → x < 2 ^ (w - 1) →
      -2 ^ (w - 1) ≤ qS w d m x ∧ qS w d m x < 2 ^ (w - 1) ∧
      qS w d m x / 2 ^ s + (if qS w d m x / 2 ^ s < 0 then 1 else 0) = x.tdiv d

/-- `Isle.Opt.Rust.magicS`'s numbers have the facts, for every signed `w`-bit divisor whose
absolute value is at least 2 and not a power of two. -/
theorem magicS_facts {w : Nat} {d : Int} (hw : 3 ≤ w) (hd0 : d ≠ 0) (hdlo : -2 ^ (w - 1) ≤ d)
    (hdhi : d < 2 ^ (w - 1)) (hpow : ∀ k, d.natAbs ≠ 2 ^ k) :
    MagicFactsS w d (Isle.Opt.Rust.magicS w d).1 (Isle.Opt.Rust.magicS w d).2.toNat := by
  obtain ⟨m, s, he, h1, h2, h3, h4⟩ := Opt.Proof.DivConst.magicS_spec hw hd0 hdlo hdhi hpow
  rw [he]
  simp only [Int.toNat_natCast]
  exact ⟨h1, h2, h3, h4⟩

theorem ofNat_toInt_small {w k : Nat} (hw : 1 ≤ w) (hk : k < w) :
    (BitVec.ofNat w k).toInt = k := by
  rw [BitVec.toInt_ofNat']
  have h1 : k < 2 ^ (w - 1) := Nat.lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := w - 1))
  apply Opt.Proof.sdc_bmod_of_range hw <;> rw [Opt.Proof.sdc_two_pow_int] <;> omega

theorem sshr_ofNat_zero {w : Nat} (q : BitVec w) : Sem.sshr q (BitVec.ofNat w 0) = q := by
  unfold Sem.sshr Sem.shiftAmt
  simp

theorem eval_sshr {Y : Frame} {m : Mem} {ty : Ty} {x s : ValueId} {a : BitVec ty.width}
    {vs : Val} (hx : Y.regs x = some ⟨ty, a⟩) (hs : Y.regs s = some vs) :
    evalInst Y m (.binary .sshr ty x s) = .ok ([⟨ty, Sem.sshr a vs.bits⟩], m) := by
  simp only [evalInst, getAs_of_regs hx, Res.ok_bind]
  simp [Frame.get, hs, Res.ofOption, BinaryOp.isShift, Sem.shift]
  try rfl

theorem RunS.sshr {T : Frame} {r r2 : Regs} {v x y : ValueId} {ty : Ty} {a : BitVec ty.width}
    {vs : Val} {ss : List Stmt} (hx : r x = some ⟨ty, a⟩) (hy : r y = some vs)
    (h : RunS T (r.set v ⟨ty, Sem.sshr a vs.bits⟩) ss r2) :
    RunS T r (⟨[v], .binary .sshr ty x y⟩ :: ss) r2 :=
  .cons (fun _ => eval_sshr (Y := { T with regs := r }) hx hy) rfl h

theorem sFix_noCall (ty : Ty) (x : ValueId) (d m : Int) (n : ValueId) :
    ∀ st ∈ (sFix ty x d m n).1, ∀ fn args, st.inst ≠ .call fn args := by
  unfold sFix
  split <;> (try split) <;> simp

theorem sShift_noCall (ty : Ty) (s : Nat) (q2 n : ValueId) :
    ∀ st ∈ (sShift ty s q2 n).1, ∀ fn args, st.inst ≠ .call fn args := by
  unfold sShift
  split <;> simp

theorem sQuot_noCall (ty : Ty) (x : ValueId) (d m : Int) (s : Nat) (n dst : ValueId) :
    ∀ st ∈ (sQuot ty x d m s n dst).1, ∀ fn args, st.inst ≠ .call fn args := by
  have hf := sFix_noCall ty x d m n
  have hs := sShift_noCall ty s (sFix ty x d m n).2 n
  intro st hst
  simp only [sQuot, List.mem_append] at hst
  rcases hst with ((h | h) | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  · exact hf st h
  · exact hs st h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp

/-- `q1 = smulhi x, m` and the fix-up run to `q2 = qS w d m x` in `(sFix …).2`. -/
theorem sFix_run (T : Frame) {r : Regs} {ty : Ty} {x n : Nat} {a : BitVec ty.width}
    {d m : Int} (hx : r x = some ⟨ty, a⟩) (hxn : x < n)
    (hm1 : -2 ^ (ty.width - 1) ≤ m) (hm2 : m < 2 ^ (ty.width - 1))
    (h1 : -2 ^ (ty.width - 1) ≤ qS ty.width d m a.toInt)
    (h2 : qS ty.width d m a.toInt < 2 ^ (ty.width - 1)) :
    ∃ r1 q2, RunS T r ([⟨[n], .iconst ty (BitVec.ofInt _ m)⟩, ⟨[n + 1], .binary .smulhi ty x n⟩] ++
        (sFix ty x d m n).1) r1 ∧ r1 (sFix ty x d m n).2 = some ⟨ty, q2⟩ ∧
      q2.toInt = qS ty.width d m a.toInt ∧ n ≤ (sFix ty x d m n).2 ∧ (sFix ty x d m n).2 < n + 3 ∧
      ∀ w, w < n → r1 w = r w := by
  have hw := ty_width_ge ty
  have hM : (BitVec.ofInt ty.width m).toInt = m := by
    rw [BitVec.toInt_ofInt]; exact Opt.Proof.sdc_bmod_of_range (by omega) hm1 hm2
  have hx0 : x ≠ n := by omega
  have hx1 : x ≠ n + 1 := by omega
  unfold sFix
  unfold qS at h1 h2 ⊢
  by_cases hA : 0 < d ∧ m < 0
  · simp only [if_pos hA] at h1 h2 ⊢
    refine ⟨_, _, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofInt ty.width m) rfl ?_ ?_
      (RunS.bin (a := Sem.binary .smulhi a (BitVec.ofInt ty.width m)) (c := a) rfl ?_ ?_ (.nil _))),
      by simp [Regs.set], Opt.Proof.sdc_q2_add (w := ty.width) (by omega) hM h1 h2, by simp, by simp, ?_⟩
    · simp [Regs.set, hx0, hx]
    · simp [Regs.set]
    · simp [Regs.set]
    · simp [Regs.set, hx0, hx1, hx]
    · intro w hw'
      have h0 : w ≠ n := by omega
      have h1' : w ≠ n + 1 := by omega
      have h2' : w ≠ n + 2 := by omega
      simp [Regs.set, h0, h1', h2']
  · by_cases hB : d < 0 ∧ 0 < m
    · simp only [if_neg hA, if_pos hB] at h1 h2 ⊢
      refine ⟨_, _, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofInt ty.width m) rfl ?_ ?_
        (RunS.bin (a := Sem.binary .smulhi a (BitVec.ofInt ty.width m)) (c := a) rfl ?_ ?_
        (.nil _))), by simp [Regs.set], Opt.Proof.sdc_q2_sub (w := ty.width) (by omega) hM h1 h2, by simp,
        by simp, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · simp [Regs.set]
      · simp [Regs.set, hx0, hx1, hx]
      · intro w hw'
        have h0 : w ≠ n := by omega
        have h1' : w ≠ n + 1 := by omega
        have h2' : w ≠ n + 2 := by omega
        simp [Regs.set, h0, h1', h2']
    · simp only [if_neg hA, if_neg hB] at h1 h2 ⊢
      refine ⟨_, _, RunS.iconst (RunS.bin (a := a) (c := BitVec.ofInt ty.width m) rfl ?_ ?_
        (.nil _)), by simp [Regs.set], Opt.Proof.sdc_q2_none (w := ty.width) (by omega) hM, by simp, by simp, ?_⟩
      · simp [Regs.set, hx0, hx]
      · simp [Regs.set]
      · intro w hw'
        have h0 : w ≠ n := by omega
        have h1' : w ≠ n + 1 := by omega
        simp [Regs.set, h0, h1']

/-- `q3 = q2 >>ₛ s` runs (or is `q2` for `s = 0`). -/
theorem sShift_run (T : Frame) {r1 : Regs} {ty : Ty} {s q2v n : Nat} {q2 : BitVec ty.width}
    (hq : r1 q2v = some ⟨ty, q2⟩) (hqn : q2v < n + 3) :
    ∃ r2, RunS T r1 (sShift ty s q2v n).1 r2 ∧
      r2 (sShift ty s q2v n).2 = some ⟨ty, Sem.sshr q2 (BitVec.ofNat ty.width s)⟩ ∧
      (sShift ty s q2v n).2 < n + 5 ∧ ∀ w, w < n + 3 → r2 w = r1 w := by
  by_cases hs : s = 0
  · subst hs
    simp only [sShift]
    exact ⟨r1, .nil _, by rw [sshr_ofNat_zero]; exact hq, Nat.lt_of_lt_of_le hqn (by omega),
      fun _ _ => rfl⟩
  · simp only [sShift, if_neg hs]
    have hq3 : q2v ≠ n + 3 := by omega
    refine ⟨_, RunS.iconst (RunS.sshr (a := q2) (vs := ⟨ty, BitVec.ofNat ty.width s⟩) ?_ ?_
      (.nil _)), by simp [Regs.set], Nat.lt_succ_self _, ?_⟩
    · simp [Regs.set, hq3, hq]
    · simp [Regs.set]
    · intro w hw
      have h3 : w ≠ n + 3 := by omega
      have h4 : w ≠ n + 4 := by omega
      simp [Regs.set, h3, h4]

/-- **The signed quotient by the magic numbers runs** to `a sdiv b` in `dst`, its temporaries
(from `n` on) the only other registers written. -/
theorem sQuot_run (T : Frame) {r : Regs} {ty : Ty} {x : Nat} {a b : BitVec ty.width} {d m : Int}
    {s n dst : Nat} (hx : r x = some ⟨ty, a⟩) (hxn : x < n) (hf : MagicFactsS ty.width d m s)
    (hd : b.toInt = d) (hb : b ≠ -1#ty.width) :
    ∃ r2, RunS T r (sQuot ty x d m s n dst).1 r2 ∧ r2 dst = some ⟨ty, a.sdiv b⟩ ∧
      ∀ w, w < n → w ≠ dst → r2 w = r w := by
  have hw := ty_width_ge ty
  obtain ⟨hm1, hm2, hs, hq⟩ := hf
  obtain ⟨ha1, ha2⟩ := Opt.Proof.sdc_toInt_range (by omega) a
  obtain ⟨hq1, hq2, hqd⟩ := hq a.toInt ha1 ha2
  show ∃ r2, RunS T r ((([⟨[n], .iconst ty (BitVec.ofInt _ m)⟩, ⟨[n + 1], .binary .smulhi ty x n⟩] ++
      (sFix ty x d m n).1) ++ (sShift ty s (sFix ty x d m n).2 n).1) ++
      [⟨[n + 5], .iconst ty (BitVec.ofNat _ (ty.width - 1))⟩,
        ⟨[n + 6], .binary .ushr ty (sShift ty s (sFix ty x d m n).2 n).2 (n + 5)⟩,
        ⟨[dst], .binary .iadd ty (sShift ty s (sFix ty x d m n).2 n).2 (n + 6)⟩]) r2 ∧
      r2 dst = some ⟨ty, a.sdiv b⟩ ∧ ∀ w, w < n → w ≠ dst → r2 w = r w
  obtain ⟨r1, q2, hr1, hq2v, hq2i, hn1, hn2, hfr1⟩ :=
    sFix_run T (n := n) (d := d) hx hxn hm1 hm2 hq1 hq2
  obtain ⟨r2, hr2, hq3v, hn3, hfr2⟩ := sShift_run T (s := s) hq2v hn2
  generalize hq3 : Sem.sshr q2 (BitVec.ofNat ty.width s) = q3 at hq3v
  have hdst : Sem.binary .iadd q3 (Sem.ushr q3 (BitVec.ofNat ty.width (ty.width - 1))) =
      a.sdiv b := by
    rw [← hq3]
    exact (Opt.Proof.sdc_sdiv_seq (w := ty.width) (by omega)
      (ofNat_toInt_small (w := ty.width) (by omega) hs) hs
      (ofNat_toInt_small (w := ty.width) (by omega) (by omega)) hb hq2i
      (by rw [hd]; exact hqd)).symm
  generalize sShift ty s (sFix ty x d m n).2 n = H at hr2 hq3v hn3 ⊢
  have h5 : H.2 ≠ n + 5 := Nat.ne_of_lt hn3
  have h6 : H.2 ≠ n + 6 := Nat.ne_of_lt (Nat.lt_trans hn3 (Nat.lt_succ_self _))
  refine ⟨_, (hr1.app hr2).app (RunS.iconst (RunS.ushr (a := q3)
    (vs := ⟨ty, BitVec.ofNat ty.width (ty.width - 1)⟩) ?_ ?_ (RunS.bin (a := q3)
    (c := Sem.ushr q3 (BitVec.ofNat ty.width (ty.width - 1))) rfl ?_ ?_ (.nil _)))), ?_, ?_⟩
  · simp [Regs.set, h5, hq3v]
  · simp [Regs.set]
  · simp [Regs.set, h5, h6, hq3v]
  · simp [Regs.set]
  · simp only [Regs.set_same]; exact congrArg (fun z => (some (Val.mk ty z) : Option Val)) hdst
  · intro w hw' hwd
    have h0 : w ≠ n + 5 := by omega
    have h1' : w ≠ n + 6 := by omega
    simp only [Regs.set, hwd, h0, h1', if_false]
    rw [hfr2 w (by omega), hfr1 w hw']

theorem magicStmtsS_noCall (op : DivOp) (ty : Ty) (v x y : ValueId) (d m : Int) (s n : Nat) :
    ∀ st ∈ (magicStmtsS op ty v x y d m s n).1, ∀ fn args, st.inst ≠ .call fn args := by
  intro st hst fn args h
  unfold magicStmtsS at hst
  split at hst
  · exact sQuot_noCall ty x d m s n v st hst fn args h
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with hst | hst | hst
    · exact sQuot_noCall ty x d m s (n + 1) n st hst fn args h
    · subst hst; cases h
    · subst hst; cases h

theorem magicStmtsS_mem_v (op : DivOp) (ty : Ty) (v x y : ValueId) (d m : Int) (s n : Nat) :
    ∃ st ∈ (magicStmtsS op ty v x y d m s n).1, v ∈ st.results := by
  unfold magicStmtsS
  split
  · exact ⟨⟨[v], .binary .iadd ty (sShift ty s (sFix ty x d m n).2 n).2 (n + 6)⟩, by simp [sQuot],
      by simp⟩
  · exact ⟨⟨[v], .binary .isub ty x (n + 1 + (sQuot ty x d m s (n + 1) n).2)⟩, by simp, by simp⟩

/-- **The statements of a signed division by magic numbers run** to the division's value in `v`,
the values from `n` on the only other registers written. -/
theorem magicStmtsS_run (T : Frame) {r : Regs} {op : DivOp} {ty : Ty} {v x y : Nat}
    {a b : BitVec ty.width} {d m : Int} {s n : Nat} (hop : op = .sdiv ∨ op = .srem)
    (hx : r x = some ⟨ty, a⟩) (hy : r y = some ⟨ty, b⟩) (hxn : x < n) (hyn : y < n)
    (hd : b.toInt = d) (hd2 : 2 ≤ d.natAbs) (hf : MagicFactsS ty.width d m s)
    {res : BitVec ty.width} (hres : Sem.div op a b = .ok res) :
    ∃ r2, RunS T r (magicStmtsS op ty v x y d m s n).1 r2 ∧ r2 v = some ⟨ty, res⟩ ∧
      ∀ w, w < n → w ≠ v → r2 w = r w := by
  have hw := ty_width_ge ty
  have hb1 : b ≠ -1#ty.width := Opt.Proof.sdc_ne_neg_one (by omega) (by omega)
  have hb0 : b ≠ 0 := by intro h; rw [h] at hd; simp at hd; omega
  have hbo : b ≠ BitVec.allOnes ty.width := by rw [← BitVec.neg_one_eq_allOnes]; exact hb1
  unfold magicStmtsS
  cases op <;> simp only [reduceCtorEq, or_self, or_false, false_or] at hop
  · simp only [ite_true]
    have hr : res = a.sdiv b := by
      simp only [Sem.div, Sem.sdiv, if_neg hb0, hbo, and_false, if_false, Except.ok.injEq] at hres
      exact hres.symm
    subst hr
    exact sQuot_run T hx hxn hf hd hb1
  · simp only [reduceCtorEq, ite_false]
    have hr : res = a.srem b := by
      simp only [Sem.div, Sem.srem, if_neg hb0, Except.ok.injEq] at hres; exact hres.symm
    subst hr
    obtain ⟨r1, h1, hq, hfr⟩ := sQuot_run T (n := n + 1) (dst := n) hx (by omega) hf hd hb1
    have hx1 : r1 x = some ⟨ty, a⟩ := by rw [hfr x (by omega) (by omega), hx]
    have hy1 : r1 y = some ⟨ty, b⟩ := by rw [hfr y (by omega) (by omega), hy]
    generalize hk : (sQuot ty x d m s (n + 1) n).2 = k
    have hxk : x ≠ n + 1 + k := by omega
    refine ⟨_, h1.app (RunS.bin rfl hq hy1
      (RunS.bin (a := a) (c := Sem.binary .imul (a.sdiv b) b) rfl ?_ ?_ (.nil _))), ?_, ?_⟩
    · simp [Regs.set, hxk, hx1]
    · simp [Regs.set]
    · simp only [Regs.set_same]
      rw [Opt.Proof.sdc_srem_of_sdiv (by omega) a b hb1]
      rfl
    · intro w hw hwv
      have h0 : w ≠ n + 1 + k := by omega
      simp only [Regs.set, hwv, h0, if_false]
      exact hfr w (by omega) (by omega)

/-- What `magicRw` does with a statement it rewrites. -/
theorem magicRw_spec {K : ValueId → Option Val} {n : ValueId} {st : Stmt} {xs : List Stmt}
    {k : Nat} (h : magicRw K n st = some (xs, k)) :
    ∃ v op ty x y c, st = ⟨[v], .div op ty x y⟩ ∧ K y = some c ∧ c.ty = ty ∧
      (((op = .udiv ∨ op = .urem) ∧ 2 ≤ c.bits.toNat ∧ log2Exact c.bits.toNat = none ∧
        (xs, k) = magicStmts op ty v x y (Isle.Opt.Rust.magicU ty.width c.bits.toNat).1
          (Isle.Opt.Rust.magicU ty.width c.bits.toNat).2.1
          (Isle.Opt.Rust.magicU ty.width c.bits.toNat).2.2.toNat n) ∨
       ((op = .sdiv ∨ op = .srem) ∧ 2 ≤ c.bits.toInt.natAbs ∧
        log2Exact c.bits.toInt.natAbs = none ∧
        (xs, k) = magicStmtsS op ty v x y c.bits.toInt (Isle.Opt.Rust.magicS ty.width c.bits.toInt).1
          (Isle.Opt.Rust.magicS ty.width c.bits.toInt).2.toNat n)) := by
  obtain ⟨rs, i⟩ := st
  unfold magicRw at h
  dsimp only at h
  split at h
  · rename_i _ _ v op ty x y
    split at h
    · rename_i c hc
      split at h
      · rename_i hcond
        obtain ⟨hty, hop, -, hd2, hlog⟩ := hcond
        simp only [Option.some.injEq] at h
        exact ⟨v, op, ty, x, y, c, rfl, hc, hty, .inl ⟨hop, hd2, hlog, h.symm⟩⟩
      · split at h
        · rename_i _ hcond
          obtain ⟨hty, hop, -, hd2, hlog⟩ := hcond
          simp only [Option.some.injEq] at h
          exact ⟨v, op, ty, x, y, c, rfl, hc, hty, .inr ⟨hop, hd2, hlog, h.symm⟩⟩
        · cases h
    · cases h
  · cases h

/-! ## Rewritten bodies and blocks -/

section
variable (K : ValueId → Option Val) (F : Nat)

/-- `yb` is `xb`, or `xb` rewritten with new values from some `n ≥ F` on. -/
def BodyRelM (xb yb : List Stmt) : Prop :=
  yb = xb ∨ ∃ n, F ≤ n ∧ yb = (magicBody K xb n).1

/-- A block and its rewritten copy. -/
def BlockRelM (B B' : Block) : Prop :=
  B'.id = B.id ∧ B'.params = B.params ∧ B'.term = B.term ∧ BodyRelM K F B.body B'.body

end

theorem magicBody_ge {K : ValueId → Option Val} :
    ∀ (ss : List Stmt) (n : ValueId), n ≤ (magicBody K ss n).2
  | [], n => Nat.le_refl n
  | st :: ss, n => by
    unfold magicBody
    split
    · exact Nat.le_trans (Nat.le_add_right _ _) (magicBody_ge ss _)
    · exact magicBody_ge ss n

theorem bodyRelM_nil {K : ValueId → Option Val} {F : Nat} {yb : List Stmt}
    (h : BodyRelM K F [] yb) : yb = [] := by
  rcases h with h | ⟨n, -, h⟩
  · exact h
  · rw [h]; rfl

theorem bodyRelM_cons {K : ValueId → Option Val} {F : Nat} {st : Stmt} {ss yb : List Stmt}
    (h : BodyRelM K F (st :: ss) yb) :
    (∃ yr, yb = st :: yr ∧ BodyRelM K F ss yr) ∨
    (∃ n xs k yr, F ≤ n ∧ magicRw K n st = some (xs, k) ∧ yb = xs ++ yr ∧ BodyRelM K F ss yr) := by
  rcases h with h | ⟨n, hn, h⟩
  · exact .inl ⟨ss, h, .inl rfl⟩
  · unfold magicBody at h
    split at h
    · rename_i xs k hw
      exact .inr ⟨n, xs, k, _, hn, hw, h, .inr ⟨n + k, by omega, rfl⟩⟩
    · exact .inl ⟨_, h, .inr ⟨n, hn, rfl⟩⟩

/-- Every result of a body is a result of its rewritten copy. -/
theorem magicBody_results {K : ValueId → Option Val} :
    ∀ (ss : List Stmt) (n : ValueId), ∀ st ∈ ss, ∀ r ∈ st.results,
      ∃ st' ∈ (magicBody K ss n).1, r ∈ st'.results
  | [], _, st, hst, _, _ => by cases hst
  | st0 :: ss, n, st, hst, r, hr => by
    unfold magicBody
    split
    · rename_i xs k hw
      rcases List.mem_cons.1 hst with rfl | hst
      · obtain ⟨v, op, ty, x, y, c, rfl, -, -, hcase⟩ := magicRw_spec hw
        simp only [List.mem_singleton] at hr
        subst hr
        rcases hcase with ⟨-, -, -, hxs⟩ | ⟨-, -, -, hxs⟩
        · generalize Isle.Opt.Rust.magicU ty.width c.bits.toNat = mg at hxs
          have hx1 : xs = (magicStmts op ty r x y mg.1 mg.2.1 mg.2.2.toNat n).1 := by rw [← hxs]
          obtain ⟨st', h1, h2⟩ := magicStmts_mem_v op ty r x y mg.1 mg.2.1 mg.2.2.toNat n
          exact ⟨st', List.mem_append_left _ (hx1 ▸ h1), h2⟩
        · generalize Isle.Opt.Rust.magicS ty.width c.bits.toInt = mg at hxs
          have hx1 : xs = (magicStmtsS op ty r x y c.bits.toInt mg.1 mg.2.toNat n).1 := by
            rw [← hxs]
          obtain ⟨st', h1, h2⟩ := magicStmtsS_mem_v op ty r x y c.bits.toInt mg.1 mg.2.toNat n
          exact ⟨st', List.mem_append_left _ (hx1 ▸ h1), h2⟩
      · obtain ⟨st', h1, h2⟩ := magicBody_results ss _ st hst r hr
        exact ⟨st', List.mem_append_right _ h1, h2⟩
    · rcases List.mem_cons.1 hst with rfl | hst
      · exact ⟨_, List.mem_cons_self .., hr⟩
      · obtain ⟨st', h1, h2⟩ := magicBody_results ss _ st hst r hr
        exact ⟨st', List.mem_cons_of_mem _ h1, h2⟩

theorem magicBlocks_find {K : ValueId → Option Val} {bs : List BlockId} {F : Nat} (id : BlockId) :
    ∀ (bl : List Block) (n : ValueId), F ≤ n →
      match bl.find? (·.id == id) with
      | none => (magicBlocks K bs bl n).find? (·.id == id) = none
      | some B => ∃ B', (magicBlocks K bs bl n).find? (·.id == id) = some B' ∧ BlockRelM K F B B'
  | [], _, _ => rfl
  | b :: rest, n, hn => by
    have ih := magicBlocks_find (K := K) (bs := bs) (F := F) id rest
    by_cases hb : (b.id == id) = true
    · have hfb : (b :: rest).find? (·.id == id) = some b := by simp [hb]
      rw [hfb]
      by_cases hc : bs.contains b.id = true
      · refine ⟨{ b with body := (magicBody K b.body n).1 }, ?_, rfl, rfl, rfl, .inr ⟨n, hn, rfl⟩⟩
        simp [magicBlocks, List.contains_iff_mem.1 hc, hb]
      · refine ⟨b, ?_, rfl, rfl, rfl, .inl rfl⟩
        have hc' : b.id ∉ bs := fun h => hc (List.contains_iff_mem.2 h)
        simp [magicBlocks, hc', hb]
    · have hb' : (b.id == id) = false := by simpa using hb
      have hfb : (b :: rest).find? (·.id == id) = rest.find? (·.id == id) := by
        simp [hb']
      rw [hfb]
      by_cases hc : bs.contains b.id = true
      · have hd : (magicBlocks K bs (b :: rest) n).find? (·.id == id) =
            (magicBlocks K bs rest (magicBody K b.body n).2).find? (·.id == id) := by
          simp [magicBlocks, List.contains_iff_mem.1 hc, hb']
        rw [hd]
        exact ih _ (Nat.le_trans hn (magicBody_ge _ _))
      · have hd : (magicBlocks K bs (b :: rest) n).find? (·.id == id) =
            (magicBlocks K bs rest n).find? (·.id == id) := by
          have hc' : b.id ∉ bs := fun h => hc (List.contains_iff_mem.2 h)
          simp [magicBlocks, hc', hb']
        rw [hd]
        exact ih _ hn

theorem magicBlocks_head {K : ValueId → Option Val} {bs : List BlockId} {F : Nat}
    {bl : List Block} {n : ValueId} (hn : F ≤ n) {B : Block} (h : bl.head? = some B) :
    ∃ B', (magicBlocks K bs bl n).head? = some B' ∧ BlockRelM K F B B' := by
  cases bl with
  | nil => cases h
  | cons b rest =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    unfold magicBlocks
    split
    · exact ⟨_, rfl, rfl, rfl, rfl, .inr ⟨n, hn, rfl⟩⟩
    · exact ⟨_, rfl, rfl, rfl, rfl, .inl rfl⟩

theorem magicBlocks_mem {K : ValueId → Option Val} {bs : List BlockId} {F : Nat} :
    ∀ (bl : List Block) (n : ValueId), F ≤ n → ∀ b ∈ bl,
      ∃ b' ∈ magicBlocks K bs bl n, BlockRelM K F b b'
  | [], _, _, b, hb => by cases hb
  | b0 :: rest, n, hn, b, hb => by
    unfold magicBlocks
    split
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self .., rfl, rfl, rfl, .inr ⟨n, hn, rfl⟩⟩
      · obtain ⟨b', h1, h2⟩ := magicBlocks_mem rest _ (Nat.le_trans hn (magicBody_ge _ _)) b hb
        exact ⟨b', List.mem_cons_of_mem _ h1, h2⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self .., rfl, rfl, rfl, .inl rfl⟩
      · obtain ⟨b', h1, h2⟩ := magicBlocks_mem rest _ hn b hb
        exact ⟨b', List.mem_cons_of_mem _ h1, h2⟩

section
variable {f : Function} {K : ValueId → Option Val} {bs : List BlockId} {n : ValueId}

@[simp] theorem magicFn_globals : (magicFn f K bs n).globals = f.globals := rfl
@[simp] theorem magicFn_externs : (magicFn f K bs n).externs = f.externs := rfl
@[simp] theorem magicFn_sig : (magicFn f K bs n).sig = f.sig := rfl
@[simp] theorem magicFn_sigDecls : (magicFn f K bs n).sigDecls = f.sigDecls := rfl
@[simp] theorem magicFn_slots : (magicFn f K bs n).slots = f.slots := rfl
@[simp] theorem magicFn_name : (magicFn f K bs n).name = f.name := rfl

theorem magicFn_block? {F : Nat} (hn : F ≤ n) {id : BlockId} {B : Block}
    (h : f.block? id = some B) :
    ∃ B', (magicFn f K bs n).block? id = some B' ∧ BlockRelM K F B B' := by
  have := magicBlocks_find (K := K) (bs := bs) (F := F) id f.blocks n hn
  unfold Function.block? at h
  rw [h] at this
  exact this

/-- The rewritten function's fresh value is at least `f`'s: every parameter and result of `f`
is one of it. -/
theorem magicFn_freshValue_ge : f.freshValue ≤ (magicFn f K bs n).freshValue := by
  apply freshValue_le_of_bound
  intro b hb
  obtain ⟨b', hb', -, hpar, -, hbody⟩ := magicBlocks_mem (K := K) (bs := bs) (F := 0) f.blocks n
    (Nat.zero_le _) b hb
  have hlt := lt_freshValue (f := magicFn f K bs n) hb'
  refine ⟨fun p hp => hlt.1 p (hpar ▸ hp), fun st hst r hr => ?_⟩
  rcases hbody with h | ⟨n', -, h⟩
  · exact hlt.2 st (h ▸ hst) r hr
  · obtain ⟨st', h1, h2⟩ := magicBody_results (K := K) b.body n' st hst r hr
    exact hlt.2 st' (h ▸ h1) r h2

end

/-! ## The frame relation -/

section
variable {f : Function} {K : ValueId → Option Val} {bs : List BlockId}

variable (f K bs) in
/-- The frame relation (module doc). -/
def MagR (X Y : Frame) : Prop :=
  X.func = f ∧ Y.func = magicFn f K bs f.freshValue ∧ KInv K X.regs ∧ Y.slots = X.slots ∧
    Agree (· < f.freshValue) X.regs Y.regs ∧ Y.term = X.term ∧
    ∃ b ∈ f.blocks, X.body <:+ b.body ∧ X.term = b.term ∧ BodyRelM K f.freshValue X.body Y.body

/-- The values `f` reads and defines are below its fresh value. -/
theorem refsOk_lt (hR : refsOk f = true) {b : Block} (hb : b ∈ f.blocks) :
    (∀ st ∈ b.body, (∀ v ∈ operands st.inst, v < f.freshValue) ∧
      ∀ v ∈ st.results, v < f.freshValue) ∧
    ∀ v ∈ termOperands b.term, v < f.freshValue :=
  ⟨fun st hst => ⟨(refsOk_spec hR hb).1 st hst, (lt_freshValue hb).2 st hst⟩,
    (refsOk_spec hR hb).2⟩

/-- Entering a block: its rewritten copy, with arguments read alike. -/
theorem MagR.enter (hk : kOk f K = true) {A A1 B : Frame} {bc bc' : BlockCall}
    (hA : A.func = f) (hB : B.func = magicFn f K bs f.freshValue) (hI : KInv K A.regs)
    (hsl : B.slots = A.slots) (hag : Agree (· < f.freshValue) A.regs B.regs)
    (hblk : bc'.block = bc.block)
    (hga : ∀ args, A.getMany bc.args = .ok args → B.getMany bc'.args = .ok args)
    (he : enterBlock A bc = .ok A1) :
    ∃ B1, enterBlock B bc' = .ok B1 ∧ MagR f K bs A1 B1 := by
  obtain ⟨Bk, args, regs, hBk, hga0, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hA] at hBk
  obtain ⟨Bk', hBk', -, hpar, hterm, hbody⟩ :=
    magicFn_block? (K := K) (bs := bs) (F := f.freshValue) (Nat.le_refl _) hBk
  have hBm : Bk ∈ f.blocks := List.mem_of_find?_eq_some hBk
  obtain ⟨regs', hset', hag'⟩ := setMany_agree hag (hpar ▸ hset)
  refine ⟨_, enterBlock_of (fr := B) (by rw [hB, hblk]; exact hBk') (hga args hga0)
    (by rw [hpar]; exact hty) hset', hA, hB, kInv_set hI (fun x hx => ?_) hset, hsl, hag', hterm,
    Bk, hBm, List.suffix_refl _, rfl, hbody⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact (kOk_spec hk hBm).1 p hp

/-- **A rewritten division**: the source's step is matched by the rewritten statements. -/
theorem magic_step {F : Nat} {X Y : Frame} {m : Mem} {st : Stmt} {ss yr xs : List Stmt}
    {n k : Nat} (hw : magicRw K n st = some (xs, k)) (hFn : F ≤ n) (hXb : X.body = st :: ss)
    (hYb : Y.body = xs ++ yr) (hI : KInv K X.regs) (hag : Agree (· < F) X.regs Y.regs)
    (hops : ∀ v ∈ operands st.inst, v < F) (hres : ∀ v ∈ st.results, v < F)
    {X1 : Frame} {m1 : Mem} (hl : lstep X m = .next X1 m1) :
    ∃ Y1, LStar Y m Y1 m1 ∧ X1 = { X with regs := X1.regs, body := ss } ∧
      Y1 = { Y with regs := Y1.regs, body := yr } ∧ Agree (· < F) X1.regs Y1.regs := by
  obtain ⟨v, op, ty, x, y, c, rfl, hc, -, hcase⟩ := magicRw_spec hw
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
      simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok] at he
      obtain ⟨a, ha, b, hb, r, hr, hvals⟩ := he
      simp only [Prod.mk.injEq] at hvals
      obtain ⟨rfl, rfl⟩ := hvals
      have hxa := getAs_regs ha
      have hyb := getAs_regs hb
      have hcb : c = ⟨ty, b⟩ := (hI y c ⟨ty, b⟩ hc hyb).symm
      subst hcb
      dsimp only at hcase
      have hxF : x < F := hops x (by simp [operands])
      have hyF : y < F := hops y (by simp [operands])
      have hvF : v < F := hres v (by simp)
      have hYx : Y.regs x = some ⟨ty, a⟩ := (hag x hxF).trans hxa
      have hYy : Y.regs y = some ⟨ty, b⟩ := (hag y hyF).trans hyb
      have hxn := Nat.lt_of_lt_of_le hxF hFn
      have hyn := Nat.lt_of_lt_of_le hyF hFn
      have hr1 : r1 = X.regs.set v ⟨ty, r⟩ := by
        simp only [Regs.setMany, Option.some.injEq] at hs
        exact hs.symm
      subst hr1
      have hw8 := ty_width_ge ty
      have hYeq : ({ Y with regs := Y.regs, body := xs ++ yr } : Frame) = Y := by rw [← hYb]
      obtain ⟨r2, hstar, hv, hfr⟩ : ∃ r2, LStar Y m { Y with regs := r2, body := yr } m ∧
          r2 v = some ⟨ty, r⟩ ∧ ∀ w, w < n → w ≠ v → r2 w = Y.regs w := by
        rcases hcase with ⟨hop, hd2, hlog, hxs⟩ | ⟨hop, hd2, hlog, hxs⟩
        · have hf := magicU_facts (by omega) hd2 b.isLt (log2Exact_none hlog)
          generalize Isle.Opt.Rust.magicU ty.width b.toNat = mg at hf hxs
          obtain ⟨r2, hrun, hv, hfr⟩ :=
            magicStmts_run Y (v := v) (n := n) hop hYx hYy hxn hyn hd2 hf (ofExcept_ok hr)
          have hxs' : xs = (magicStmts op ty v x y mg.1 mg.2.1 mg.2.2.toNat n).1 := by rw [← hxs]
          have hstar := hrun.lstar (magicStmts_noCall op ty v x y mg.1 mg.2.1 mg.2.2.toNat n) yr m
          rw [← hxs', hYeq] at hstar
          exact ⟨r2, hstar, hv, hfr⟩
        · obtain ⟨hlo, hhi⟩ := Opt.Proof.sdc_toInt_range (by omega) b
          have hf := magicS_facts (d := b.toInt) (by omega) (by omega) hlo hhi (log2Exact_none hlog)
          generalize Isle.Opt.Rust.magicS ty.width b.toInt = mg at hf hxs
          obtain ⟨r2, hrun, hv, hfr⟩ :=
            magicStmtsS_run Y (v := v) (n := n) hop hYx hYy hxn hyn rfl hd2 hf (ofExcept_ok hr)
          have hxs' : xs = (magicStmtsS op ty v x y b.toInt mg.1 mg.2.toNat n).1 := by
            rw [← hxs]
          have hstar := hrun.lstar (magicStmtsS_noCall op ty v x y b.toInt mg.1 mg.2.toNat n) yr m
          rw [← hxs', hYeq] at hstar
          exact ⟨r2, hstar, hv, hfr⟩
      refine ⟨_, hstar, rfl, rfl, fun w hw => ?_⟩
      dsimp only
      by_cases hwv : w = v
      · subst hwv; rw [hv]; simp [Regs.set]
      · rw [hfr w (Nat.lt_of_lt_of_le hw hFn) hwv, hag w hw]; simp [Regs.set, hwv]

/-- A rewritten division never traps, calls or leaves the frame: its divisor is a constant of
at least 2. -/
theorem magic_only_next {X : Frame} {m : Mem} {st : Stmt} {ss xs : List Stmt} {n k : Nat}
    (hw : magicRw K n st = some (xs, k)) (hXb : X.body = st :: ss) (hI : KInv K X.regs)
    {r : LRes} (hn : ∀ X1 m1, r ≠ .next X1 m1) (hs : ∀ msg, r ≠ .stuck msg) :
    lstep X m ≠ r := by
  intro hl
  obtain ⟨v, op, ty, x, y, c, rfl, hc, -, hcase⟩ := magicRw_spec hw
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
    dsimp only at hcase
    have hw8 := ty_width_ge ty
    have hok' : ∃ r, Sem.div op a b = .ok r := by
      rcases hcase with ⟨hop, hd2, -, -⟩ | ⟨hop, hd2, -, -⟩
      · have hb0 : b ≠ 0 := by intro h; rw [h] at hd2; simp at hd2
        rcases hop with rfl | rfl
        · exact ⟨a / b, by simp only [Sem.div, Sem.udiv, if_neg hb0]⟩
        · exact ⟨a % b, by simp only [Sem.div, Sem.urem, if_neg hb0]⟩
      · have hb0 : b ≠ 0 := by intro h; rw [h] at hd2; simp at hd2
        have hbo : b ≠ BitVec.allOnes ty.width := by
          rw [← BitVec.neg_one_eq_allOnes]
          exact Opt.Proof.sdc_ne_neg_one (by omega) (by omega)
        rcases hop with rfl | rfl
        · exact ⟨a.sdiv b, by simp only [Sem.div, Sem.sdiv, if_neg hb0, hbo, and_false, if_false]⟩
        · exact ⟨a.srem b, by simp only [Sem.div, Sem.srem, if_neg hb0]⟩
    obtain ⟨r, hr⟩ := hok'
    rcases h3 with h3 | ⟨r', -, h4⟩
    · rw [hr] at h3; simp [Res.ofExcept] at h3
    · simp [pure] at h4

/-- A statement step of both frames. -/
theorem MagR.stepA (hk : kOk f K = true) (hR : refsOk f = true) {X Y : Frame} {m : Mem}
    (h : MagR f K bs X Y) {st : Stmt} {ss : List Stmt} (hx : X.body = st :: ss) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, LStar Y m Y1 m1 ∧ MagR f K bs X1 Y1) ∧
    (∀ ext vals rs rest, lstep X m = .call ext vals rs rest → ∃ rest',
      lstep Y m = .call ext vals rs rest' ∧
      Cont (MagR f K bs) { X with body := rest } rs { Y with body := rest' } rs
        (AbiParam.tys ext.sig.returns)) ∧
    (∀ c, lstep X m = .trap c → lstep Y m = .trap c) := by
  obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := h
  have hst : st ∈ b.body := hsuf.subset (by rw [hx]; simp)
  have hsuf' : ss <:+ b.body := (List.suffix_cons st ss).trans (hx ▸ hsuf)
  obtain ⟨hops, hres⟩ := (refsOk_lt hR hb).1 st hst
  rw [hx] at hbr
  rcases bodyRelM_cons hbr with ⟨yr, hyb, hrel⟩ | ⟨n, xs, k, yr, hFn, hw, hyb, hrel⟩
  · -- the same statement
    by_cases hc : ∃ fn args, st.inst = .call fn args
    · obtain ⟨fn, args, hi⟩ := hc
      have hca : callArgs Y fn args = callArgs X fn args := by
        unfold callArgs
        rw [getMany_congr (fr := X) (fr' := Y)
          (fun v hv => hag v (hops v (by simp [hi, operands, hv])))]
        simp only [Function.extern?, hXf, hYf, magicFn_externs]
      rw [lstep_call hx hi, lstep_call hyb hi, hca]
      refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest h => ?_, fun c h => ?_⟩
      · cases hcx : callArgs X fn args <;> simp [hcx, LRes.ofRes] at h
      · cases hcx : callArgs X fn args with
        | ok p =>
          obtain ⟨ext', vals'⟩ := p
          simp only [hcx, LRes.ofRes, LRes.call.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨yr, by simp only [LRes.ofRes], fun vs regs _ hs => ?_⟩
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
    · obtain ⟨Y1, hstar, hX1, hY1, hag1⟩ := magic_step hw hFn hx hyb hI hag hops hres h
      obtain ⟨hI1, -⟩ := kInv_next hk hb hst hx hI h
      refine ⟨Y1, hstar, ?_⟩
      rw [hX1, hY1]
      exact ⟨hXf, hYf, hI1, hsl, hag1, hYt, b, hb, hsuf', hterm, hrel⟩
    · exact absurd h (magic_only_next hw hx hI (fun _ _ h => by cases h) (fun _ h => by cases h))
    · exact absurd h (magic_only_next hw hx hI (fun _ _ h => by cases h) (fun _ h => by cases h))

/-- Both frames at their terminators. -/
theorem MagR.stepC (hk : kOk f K = true) (hR : refsOk f = true) {X Y : Frame} {m : Mem}
    (h : MagR f K bs X Y) (hx : X.body = []) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ MagR f K bs X1 Y1) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep X m = r →
      lstep Y m = r) := by
  obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := h
  rw [hx] at hbr
  have hy : Y.body = [] := bodyRelM_nil hbr
  have hops : ∀ v ∈ termOperands X.term, v < f.freshValue := fun v hv =>
    (refsOk_lt hR hb).2 v (hterm ▸ hv)
  have henter : ∀ (bc : BlockCall), (∀ a ∈ bc.args, a < f.freshValue) → ∀ X1 m1,
      LRes.ofRes (enterBlock X bc) (fun fr => LRes.next fr m) = .next X1 m1 →
      ∃ Y1, LRes.ofRes (enterBlock Y bc) (fun fr => LRes.next fr m) = .next Y1 m1 ∧
        MagR f K bs X1 Y1 := by
    intro bc hbc X1 m1 he
    obtain ⟨he1, hm⟩ := ofRes_enter_next he
    subst hm
    obtain ⟨Y1, he', hr⟩ := MagR.enter (bs := bs) hk hXf hYf hI hsl hag rfl
      (fun args h => by
        rw [getMany_congr (fr := X) (fr' := Y) (fun v hv => hag v (hbc v hv))]; exact h)
      he1
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
    have hargs : ∀ cv : Val, ∀ v ∈ (if Sem.truthy cv.bits then t else e).args, v < f.freshValue :=
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
    have hargs : ∀ xv : Val, ∀ v ∈ (tbl[xv.toNat]?.getD d).args, v < f.freshValue :=
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
      simp only [Function.extern?, hXf, hYf, magicFn_externs, magicFn_sig]
    simp only [hta]
    refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
    cases hg : tailArgs X fn args <;> rw [hg] at h <;> cases h
  | trap tc => exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
  | tryCall fn args et =>
    exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩
  | tryCallIndirect c args et =>
    exact ⟨fun X1 m1 h => (by cases h), fun r _ hs h => absurd h.symm (hs _)⟩

/-- The window values of both frames are at or above `f.freshValue`: binding them keeps the
registers below it, and the constants' invariant. -/
theorem MagR.win_agree {X Y : Frame} (hXf : X.func = f)
    (hYf : Y.func = magicFn f K bs f.freshValue) (hK : ∀ x v, K x = some v → x < f.freshValue)
    (hI : KInv K X.regs) (hag : Agree (· < f.freshValue) X.regs Y.regs) {n : Nat} {vs : List Val}
    {regs regs' : Regs}
    (hs : X.regs.setMany (tryRets n X.func.freshValue) vs = some regs)
    (hs' : Y.regs.setMany (tryRets n Y.func.freshValue) vs = some regs') :
    Agree (· < f.freshValue) regs regs' ∧ KInv K regs := by
  have hle : f.freshValue ≤ Y.func.freshValue := by rw [hYf]; exact magicFn_freshValue_ge
  refine ⟨fun v hv => ?_, kInv_set hI (fun x hx => ?_) hs⟩
  · have h1 : v ∉ tryRets n X.func.freshValue := by
      intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
      have he' : X.func.freshValue + j = v := he
      rw [hXf] at he'; exact no_window' he' hv
    have h2 : v ∉ tryRets n Y.func.freshValue := by
      intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
      have he' : Y.func.freshValue + j = v := he
      exact no_window he' hv hle
    rw [((setMany_spec hs').2 v).1 h2, ((setMany_spec hs).2 v).1 h1]
    exact hag v hv
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    rw [hXf]
    exact kNone_window hK

/-- **The frame relation is a pass simulation with windows and handler edges.** -/
theorem MagR.isSimWU (hk : kOk f K = true) (hR : refsOk f = true)
    (hK : ∀ x v, K x = some v → x < f.freshValue) (syms : String → Option Nat) :
    IsSimWU syms (MagR f K bs) := by
  -- `try_call` successors
  have hpost : ∀ (X Y : Frame) (n : Nat) (bc bc' : BlockCall) (et : ExnTable),
      (∀ v ∈ et.normal.vals, v < f.freshValue) → MagR f K bs X Y → Win X Y →
      tryNormal et X.func.freshValue = .ok bc → tryNormal et Y.func.freshValue = .ok bc' →
      ∀ rtys, TCont (MagR f K bs) X (tryRets n X.func.freshValue) bc Y
        (tryRets n Y.func.freshValue) bc' rtys := by
    rintro X Y n bc bc' et hops' ⟨hXf, hYf, hI, hsl, hag, -⟩ hw hbc hbc' rtys vs regs _ hset
    obtain ⟨regs', hset'⟩ := setMany_len (r := Y.regs) (xs := tryRets n Y.func.freshValue)
      (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
        List.length_range] at this ⊢; exact this)
    have hW := setMany_tryRets hset
    have hW' := setMany_tryRets hset'
    obtain ⟨hagr, hI'⟩ := MagR.win_agree hXf hYf hK hI hag hset hset'
    refine ⟨regs', hset', fun X1 he => ?_⟩
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair id (et := et) (et' := et)
      (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
    rw [hbc'] at hbc2; cases hbc2
    refine MagR.enter (A := { X with regs }) (B := { Y with regs := regs' }) hk hXf hYf hI' hsl hagr
      hblk (fun args hga => getMany_pw2 (A := { X with regs }) (hpw.imp fun x y h => ?_) hga) he
    simp only
    rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
    · rw [hx, hy]; exact hagr v (hops' v hv)
    · rw [hx, hy, hW i, hW' i]
      split
      · rfl
      · exact (hw i).symm
  -- handler successors
  have hhand : ∀ (X Y : Frame) (et : ExnTable),
      (∀ d ∈ et.handlers, ∀ v ∈ d.vals, v < f.freshValue) → MagR f K bs X Y → Win X Y →
      HCont (MagR f K bs) X et Y et := by
    rintro X Y et hops' ⟨hXf, hYf, hI, hsl, hag, -⟩ hw e
    refine ⟨fun hn => catchIn_eq_none.2 (catchIn_eq_none.1 hn), fun X1 hc => ?_⟩
    obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    obtain ⟨bc', hbc', hblk, hpw⟩ := tryHandler_pair id (b2 := Y.func.freshValue) hbc
    rw [TryDest.mapVals_id] at hbc'
    obtain ⟨regs', hset'⟩ := setMany_len (r := Y.regs)
      (xs := (List.range e.payload.length).map (Y.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hW := setMany_tryRets (n := e.payload.length) (W := X.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := Y.func.freshValue) hset'
    obtain ⟨hagr, hI'⟩ := MagR.win_agree (n := e.payload.length) hXf hYf hK hI hag hset hset'
    have hd' : d ∈ et.handlers := catch?_mem hd
    refine ⟨_, catchIn_of hd hbc' hset', rfl, rfl, bc, bc', rfl, rfl, fun X2 he => ?_⟩
    have he0 : enterBlock { X with regs } bc = .ok X2 := by
      rw [← enterBlock_bt { X with regs } [] (.jump bc)]; exact he
    obtain ⟨Y2, he', hr⟩ := MagR.enter (A := { X with regs }) (B := { Y with regs := regs' }) hk hXf
      hYf hI' hsl hagr hblk (fun args hga => getMany_pw2 (A := { X with regs })
        (hpw.imp fun x y h => by
          simp only
          rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
          · rw [hx, hy]; exact hagr v (hops' d hd' v hv)
          · rw [hx, hy, hW i, hW' i]
            split
            · rfl
            · exact (hw i).symm) hga) he0
    exact ⟨Y2, (enterBlock_bt { Y with regs := regs' } [] (.jump bc') bc').trans he', hr⟩
  -- a frame at its terminator: both at the same terminator, its operands below the fresh value
  have htry : ∀ X Y, MagR f K bs X Y → X.body = [] →
      Y.body = [] ∧ Y.term = X.term ∧ ∀ v ∈ termOperands X.term, v < f.freshValue := by
    rintro X Y ⟨-, -, -, -, -, hYt, b, hb, -, hterm, hbr⟩ hx
    rw [hx] at hbr
    exact ⟨bodyRelM_nil hbr, hYt, fun v hv => (refsOk_lt hR hb).2 v (hterm ▸ hv)⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X Y ⟨hXf, hYf, -, hsl, -⟩
    exact ⟨hsl, by rw [hYf, hXf]; rfl⟩
  · rintro X Y m X1 m1 hr hm hl
    cases hx : X.body with
    | cons st rest => exact (MagR.stepA hk hR hr hx (m := m)).1 X1 m1 hl
    | nil =>
      obtain ⟨Y1, h1, h2⟩ := (MagR.stepC hk hR hr hx (m := m)).1 X1 m1 hl
      exact ⟨Y1, .single h1, h2⟩
  · rintro X Y m ext vals rs rest hr hm hl
    obtain ⟨st, fn, args, hbd, -⟩ := lstep_call_inv hl
    obtain ⟨rest', h1, h2⟩ := (MagR.stepA hk hR hr hbd (m := m)).2.1 ext vals rs rest hl
    exact ⟨Y, rs, rest', .refl _ _, h1, h2⟩
  · rintro X Y m vals hr hm hl
    exact ⟨Y, .refl _ _, (MagR.stepC hk hR hr (lstep_ret_inv hl) (m := m)).2 _
      (fun _ _ h => by cases h) (fun _ h => by cases h) hl⟩
  · rintro X Y m ext vals hr hm hl
    exact ⟨Y, .refl _ _, (MagR.stepC hk hR hr (lstep_tail_inv hl) (m := m)).2 _
      (fun _ _ h => by cases h) (fun _ h => by cases h) hl⟩
  · rintro X Y m c hr hm hl
    cases hx : X.body with
    | cons st rest => exact ⟨Y, m, .refl _ _, (MagR.stepA hk hR hr hx (m := m)).2.2 c hl⟩
    | nil =>
      exact ⟨Y, m, .refl _ _, (MagR.stepC hk hR hr hx (m := m)).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro X Y m st rest sig callee args d a vals hr - - - hm hbd hi hca
    obtain ⟨hXf, hYf, hI, hsl, hag, hYt, b, hb, hsuf, hterm, hbr⟩ := hr
    have hst : st ∈ b.body := hsuf.subset (by rw [hbd]; simp)
    obtain ⟨hops, -⟩ := (refsOk_lt hR hb).1 st hst
    rw [hbd] at hbr
    rcases bodyRelM_cons hbr with ⟨yr, hyb, hrel⟩ | ⟨n, xs, k, yr, -, hw, -, -⟩
    · refine ⟨Y, st, yr, sig, callee, args, .refl _ _, hyb, hi, ?_, ?_⟩
      · rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hops v (by simp [hi, operands, hv])))]
        simp only [Frame.get, hag callee (hops callee (by simp [hi, operands])), hXf, hYf,
          magicFn_sigDecls]
      · intro vs regs _ hset
        obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
        exact ⟨regs', hset', hXf, hYf, kInv_set hI (kOk_none hk hb hst (by rw [hi]; rfl)) hset,
          hsl, hag', hYt, b, hb, (List.suffix_cons st rest).trans (hbd ▸ hsuf), hterm, hrel⟩
    · obtain ⟨_, _, _, _, _, _, hst', -⟩ := magicRw_spec hw
      rw [hst'] at hi; cases hi
  · -- `try_call`, `try_call_indirect`
    refine ⟨?_, ?_⟩
    · rintro X Y m fn args et n base bc ext vals hr - - hw hm hbd ht htc hca
      obtain ⟨hy, hty, hopsT⟩ := htry X Y hr hbd
      have hr0 := hr
      obtain ⟨hXf, hYf, -, hsl, hag, -⟩ := hr
      rw [ht] at hopsT hty
      obtain ⟨rfl, hbc⟩ := tcArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
      have htc' : tcArgs Y fn et = .ok (n, Y.func.freshValue, bc') := by
        obtain ⟨e0, s0, he0, hs0, hc0, -, -, hn0⟩ := tcArgs_ok.1 htc
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', hn0⟩
        · rw [← he0]; simp only [Function.extern?, hYf, hXf, magicFn_externs]
        · rw [← hs0, hYf, hXf, magicFn_sigDecls]
      have hca' : callArgs Y fn args = .ok (ext, vals) := by
        rw [← hca]
        unfold callArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Function.extern?, hYf, hXf, magicFn_externs]
      refine ⟨Y, fn, args, et, _, bc', .refl _ _, hy, hty, htc', hca', ?_, ?_⟩
      · exact hpost X Y n bc bc' et (fun v hv => hopsT v (normal_vals_sub v hv)) hr0 hw hbc hbc' _
      · exact hhand X Y et (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          hr0 hw
    · rintro X Y m callee args et n base bc d a vals hr - - hw hm hbd ht htc hca
      obtain ⟨hy, hty, hopsT⟩ := htry X Y hr hbd
      have hr0 := hr
      obtain ⟨hXf, hYf, -, hsl, hag, -⟩ := hr
      rw [ht] at hopsT hty
      obtain ⟨rfl, hbc⟩ := ticArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := Y.func.freshValue) hbc
      have htc' : ticArgs Y et = .ok (n, Y.func.freshValue, bc') := by
        obtain ⟨s0, hs0, -, -, hn0⟩ := ticArgs_ok.1 htc
        exact ticArgs_ok.2 ⟨s0, by rw [← hs0, hYf, hXf, magicFn_sigDecls], rfl, hbc', hn0⟩
      have hca' : ciArgs Y et.sig callee args = .ok (d, a, vals) := by
        rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := X) (fr' := Y) (xs := args)
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Frame.get, hag callee (hopsT callee (by simp [termOperands])), hYf, hXf,
          magicFn_sigDecls]
      refine ⟨Y, callee, args, et, _, bc', .refl _ _, hy, hty, htc', hca', ?_, ?_⟩
      · exact hpost X Y n bc bc' et (fun v hv => hopsT v (normal_vals_sub' v hv)) hr0 hw hbc hbc' _
      · exact hhand X Y et (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          hr0 hw

/-- **The rewritten function simulates `f`.** -/
theorem magicFn_simU (hk : kOk f K = true) (hR : refsOk f = true)
    (hK : ∀ x v, K x = some v → x < f.freshValue) :
    FunSimU f (magicFn f K bs f.freshValue) := by
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms =>
    ⟨MagR f K bs, MagR.isSimWU hk hR hK syms, fun b hb => ?_⟩
  obtain ⟨b', hb', -, hpar, hterm, hbody⟩ :=
    magicBlocks_head (K := K) (bs := bs) (F := f.freshValue) (n := f.freshValue) (Nat.le_refl _) hb
  refine ⟨b', hb', hpar, fun args regs slots _ hset _ => ?_⟩
  have hbm : b ∈ f.blocks := List.mem_of_mem_head? hb
  refine ⟨rfl, rfl, kInv_set (kInv_empty K) (fun x hx => ?_) hset, rfl, fun _ _ => rfl,
    hterm, b, hbm, List.suffix_refl _, rfl, hbody⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact (kOk_spec hk hbm).1 p hp

end

/-- **Division by a constant with magic numbers is simulated by its input.** -/
theorem magicPre_simU (f : Function) (bs : List BlockId) : FunSimU f (magicPre f bs) := by
  unfold magicPre
  split
  · exact FunSimU.refl f
  · dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact magicFn_simU hc.1 hc.2 (fun _ _ h => kLook_lt h)
    · exact FunSimU.refl f

/-- **The folded function without its unreachable blocks is simulated by its input**
(the validator's constant-phi removal `phiPre`, divisions by constants rewritten, branches
folded, constant-phi removal). -/
theorem foldPre_simU (f : Function) (bs : List BlockId) : FunSimU f (foldPre f bs) :=
  (phiPre_simU f).trans ((divPre_simU _ bs).trans ((magicPre_simU _ bs).trans
    ((foldBr_simU _ bs).trans (ConstPhi.run_simU _))))

/-- **The folded function without its unreachable blocks, parameters kept, is simulated by its
input** (`foldPreK`: as `foldPre`, with `removeUnreachable` in place of the constant-phi removal
after the folds). -/
theorem foldPreK_simU (f : Function) (bs : List BlockId) : FunSimU f (foldPreK f bs) := by
  have h1 := (phiPre_simU f).trans ((divPre_simU _ bs).trans ((magicPre_simU _ bs).trans
    (foldBr_simU _ bs)))
  unfold foldPreK
  dsimp only
  split
  · rename_i hC
    exact h1.trans (removeUnreachable_simU _ hC)
  · exact h1

end Opt.MidVal
