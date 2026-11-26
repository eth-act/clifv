import FVTest.Opt.MidValFam5Witness

/-! # Family 6, shifts and bitwise constants: witnesses (#1119, agent MidendNext5)

Family 6 of the mid-end validator's normaliser (`FV/Opt/MidVal.lean`, proofs
`FV/Opt/Proof/MidValNormFam6.lean`, #1119 issuecomment-7200665739). Each hand-made pair is
accepted, and rejected with main's normaliser before this change (`normPrev`, `*_prev_rejects`):

* `fam6Mul`: `(x >> 3) * 8` against `x & -8` (`pos_mulShr`), `(x * 4) * 8` (the inner product
  is `x << 2`) against `x << 5` (`pos_mulShl`);
* `shAmt`: `x >> uextend.i64 y` against `x >> y` (`pos_shAmt`);
* `reStep`: `(x & 255) & 15` against `x & 15` (`pos_re`), `(x << 3) * 5` against `x * 40`
  (`pos_reShl`);
* `narrowId`: `ireduce.i8 (x & 255)` of an `i16` `x` against `ireduce.i8 x` (`pos_narrow`).

Look-alikes are rejected (`neg_*`) and are no simulations, so the re-check rejects every
certificate (`*_rejected`). The typing premise of `shAmt` is needed: it is no normaliser sound
in every frame (`shAmt_not_normSound`: a parameter declared `i64` holding an `i128` makes
`uextend.i128` of it have no value, while the shift by the parameter has one).

Real pairs (decided: rejected by main's `checkC`, accepted by `checkCertC` with the requests
`emitC` gives, with the simulation and the program refinement) are at the end.
-/

namespace Opt.MidVal.Fam6Witness
open Clif Pairs NormWitness AlgWitness CondWitness FoldWitness

/-! ## Main's normaliser (before this change) -/

/-- `narrowStep` without `narrowId`. -/
def narrowStepPrev (n : Norm) (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .ireduce ty u =>
    match nodeAt tms u with
    | some (.binary op wty a b) =>
      if ringOp op && ty.width < wty.width && tyAt aty tms a == some wty &&
          tyAt aty tms b == some wty then
        (redOf n tms ty a).bind fun a' => (redOf n tms ty b).map fun b' =>
          let j := Inst.binary op ty a' b'
          ((affStep tms j).orElse fun _ => swapStep tms j).getD (.node j)
      else none
    | _ => none
  | _ => none

/-- `Norm.base` without family 6. -/
def basePrev (f : Function) : Norm :=
  Norm.orElse (Norm.orElse Norm.std (Norm.guard (typedStep (atomTy f))))
    (Norm.orElse (Norm.guard (idStep (atomTy f)))
      (Norm.orElse (Norm.guard affStep)
        (Norm.orElse (Norm.guard swapStep) (Norm.guard (fam5Step (atomTy f))))))

def narrowPrev (f : Function) : Nat → Norm
  | 0 => basePrev f
  | k + 1 => Norm.orElse (basePrev f) (Norm.guard (narrowStepPrev (narrowPrev f k) (atomTy f)))

/-- Main's default normaliser before this change. -/
def normPrev (f : Function) : Norm := narrowPrev f 3

/-- The verdict of `check` with main's normaliser. -/
def acceptsPrev (f g : String) : Option Bool := do
  let f' := ConstPhi.run (← fn? f)
  pure (check f' (← fn? g) (normPrev f')).isOk

/-- `checkC` with main's normaliser (the same steps: hints, then the prep copies `foldPre` and
`foldPreK` for `foldCands`). -/
def checkCPrev (f g : Function) : Except Reject (List (BlockId × List Wrap)) :=
  match checkC0 f g (normPrev f) with
  | .ok h => .ok h
  | .error e =>
    let bs := match foldCands f g with
      | [] => (f.blocks.head?.map (·.id)).toList
      | bs => bs
    let prep (f' : Function) : Except Reject (List (BlockId × List Wrap)) :=
      if f'.blocks == f.blocks then .error e
      else if f'.blocks.map (·.id) != g.blocks.map (·.id) then .error e
      else match checkC0 f' g (normPrev f') with
        | .ok h => .ok (h ++ bs.map fun b => (b, []))
        | .error e' => .error e'
    if bs.isEmpty then .error e
    else match prep (foldPre f bs) with
      | .ok h => .ok h
      | .error _ => prep (foldPreK f bs)

/-- The verdict of `checkCPrev` on a decoded dump pair. -/
def realPrev (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkCPrev f g).isOk

/-! ## Shifts written as multiplications (`fam6Mul`) -/

def mulShrF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 3\n    v2 = ushr v0, v1\n    v3 = iconst.i64 8\n    v4 = imul v2, v3\n    return v4\n}"
def mulShrG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 -8\n    v4 = band v0, v5\n    return v4\n}"
def mulShrWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 -4\n    v4 = band v0, v5\n    return v4\n}"

theorem pos_mulShr : accepts mulShrF mulShrG = some true := by native_decide
theorem pos_mulShr_prev_rejects : acceptsPrev mulShrF mulShrG = some false := by native_decide
theorem neg_mulShr : accepts mulShrF mulShrWrongG = some false := by native_decide

def mulShlF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 4\n    v2 = imul v0, v1\n    v3 = iconst.i64 8\n    v4 = imul v2, v3\n    return v4\n}"
def mulShlG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 5\n    v4 = ishl v0, v5\n    return v4\n}"
def mulShlWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 6\n    v4 = ishl v0, v5\n    return v4\n}"

theorem pos_mulShl : accepts mulShlF mulShlG = some true := by native_decide
theorem pos_mulShl_prev_rejects : acceptsPrev mulShlF mulShlG = some false := by native_decide
theorem neg_mulShl : accepts mulShlF mulShlWrongG = some false := by native_decide

/-! ## Shift amounts (`shAmt`) -/

def shAmtF : String := "function %f(i64, i32) -> i64 {\nblock0(v0: i64, v1: i32):\n    v2 = uextend.i64 v1\n    v3 = ushr v0, v2\n    return v3\n}"
def shAmtG : String := "function %f(i64, i32) -> i64 {\nblock0(v0: i64, v1: i32):\n    v3 = ushr v0, v1\n    return v3\n}"
def shAmtWrongG : String := "function %f(i64, i32) -> i64 {\nblock0(v0: i64, v1: i32):\n    v3 = sshr v0, v1\n    return v3\n}"

theorem pos_shAmt : accepts shAmtF shAmtG = some true := by native_decide
theorem pos_shAmt_prev_rejects : acceptsPrev shAmtF shAmtG = some false := by native_decide
theorem neg_shAmt : accepts shAmtF shAmtWrongG = some false := by native_decide

/-! ## Constants reassociated (`reStep`) -/

def reF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 255\n    v2 = band v0, v1\n    v3 = iconst.i64 15\n    v4 = band v2, v3\n    return v4\n}"
def reG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 15\n    v4 = band v0, v5\n    return v4\n}"
def reWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 255\n    v4 = band v0, v5\n    return v4\n}"

theorem pos_re : accepts reF reG = some true := by native_decide
theorem pos_re_prev_rejects : acceptsPrev reF reG = some false := by native_decide
theorem neg_re : accepts reF reWrongG = some false := by native_decide

def reShlF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 3\n    v2 = ishl v0, v1\n    v3 = iconst.i64 5\n    v4 = imul v2, v3\n    return v4\n}"
def reShlG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 40\n    v4 = imul v0, v5\n    return v4\n}"
def reShlWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 15\n    v4 = imul v0, v5\n    return v4\n}"

theorem pos_reShl : accepts reShlF reShlG = some true := by native_decide
theorem pos_reShl_prev_rejects : acceptsPrev reShlF reShlG = some false := by native_decide
theorem neg_reShl : accepts reShlF reShlWrongG = some false := by native_decide

/-! ## A neutral constant the narrowing leaves (`narrowId`) -/

def narrowF : String := "function %f(i16) -> i8 {\nblock0(v0: i16):\n    v1 = iconst.i16 255\n    v2 = band v0, v1\n    v3 = ireduce.i8 v2\n    return v3\n}"
def narrowG : String := "function %f(i16) -> i8 {\nblock0(v0: i16):\n    v3 = ireduce.i8 v0\n    return v3\n}"
def narrowMaskF : String := "function %f(i16) -> i8 {\nblock0(v0: i16):\n    v1 = iconst.i16 127\n    v2 = band v0, v1\n    v3 = ireduce.i8 v2\n    return v3\n}"

theorem pos_narrow : accepts narrowF narrowG = some true := by native_decide
theorem pos_narrow_prev_rejects : acceptsPrev narrowF narrowG = some false := by native_decide
theorem neg_narrow : accepts narrowMaskF narrowG = some false := by native_decide

/-! ### The look-alikes are no simulations -/

def mulShrFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 3 }, { results := [2], inst := .binary .ushr .i64 0 1 },
    { results := [3], inst := .iconst .i64 8 }, { results := [4], inst := .binary .imul .i64 2 3 }] 4
def mulShrWrongGn : Function :=
  fn1 .i64 .i64 [{ results := [5], inst := .iconst .i64 (-4) },
    { results := [4], inst := .binary .band .i64 0 5 }] 4

theorem mulShrF_text : fn? mulShrF = some mulShrFn := by native_decide
theorem mulShrWrongG_text : fn? mulShrWrongG = some mulShrWrongGn := by native_decide

/-- For `x = 4`: `f` returns 0, `g` 4. -/
theorem mulShr_not_sim : ¬ FunSimMU mulShrFn mulShrWrongGn :=
  not_funSimMU_ret_ne (b := mulShrFn.blocks.head!) (b' := mulShrWrongGn.blocks.head!)
    (args := [⟨.i64, 4⟩]) (regs := Regs.empty.set 0 ⟨.i64, 4⟩) (m := Mem.empty)
    (vals := [⟨.i64, 0⟩]) (vals' := [⟨.i64, 4⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_mulShr`. -/
theorem mulShr_rejected (cert : Cert) :
    checkCert (ConstPhi.run mulShrFn) mulShrWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run mulShrFn) mulShrWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) mulShr_not_sim

def mulShlFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 4 }, { results := [2], inst := .binary .imul .i64 0 1 },
    { results := [3], inst := .iconst .i64 8 }, { results := [4], inst := .binary .imul .i64 2 3 }] 4
def mulShlWrongGn : Function :=
  fn1 .i64 .i64 [{ results := [5], inst := .iconst .i64 6 },
    { results := [4], inst := .binary .ishl .i64 0 5 }] 4

theorem mulShlF_text : fn? mulShlF = some mulShlFn := by native_decide
theorem mulShlWrongG_text : fn? mulShlWrongG = some mulShlWrongGn := by native_decide

/-- For `x = 1`: `f` returns 32, `g` 64. -/
theorem mulShl_not_sim : ¬ FunSimMU mulShlFn mulShlWrongGn :=
  not_funSimMU_ret_ne (b := mulShlFn.blocks.head!) (b' := mulShlWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, 32⟩]) (vals' := [⟨.i64, 64⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_mulShl`. -/
theorem mulShl_rejected (cert : Cert) :
    checkCert (ConstPhi.run mulShlFn) mulShlWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run mulShlFn) mulShlWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) mulShl_not_sim

/-- A function of an `i64` and an `i32` parameter returning `r` (`i64`). -/
def fn2i (body : List Stmt) (r : ValueId) : Function :=
  { name := "f", sig := { params := [ap .i64, ap .i32], returns := [ap .i64], callConv := none },
    blocks := [{ id := 0, params := [(0, .i64), (1, .i32)], cold := false, body, term := .ret [r] }] }

def shAmtFn : Function :=
  fn2i [{ results := [2], inst := .extend .uextend .i64 1 }, { results := [3], inst := .binary .ushr .i64 0 2 }] 3
def shAmtWrongGn : Function := fn2i [{ results := [3], inst := .binary .sshr .i64 0 1 }] 3

theorem shAmtF_text : fn? shAmtF = some shAmtFn := by native_decide
theorem shAmtWrongG_text : fn? shAmtWrongG = some shAmtWrongGn := by native_decide

/-- For `x = -8`, `y = 1`: `f` returns `2^63 - 4`, `g` `-4`. -/
theorem shAmt_not_sim : ¬ FunSimMU shAmtFn shAmtWrongGn :=
  not_funSimMU_ret_ne (b := shAmtFn.blocks.head!) (b' := shAmtWrongGn.blocks.head!)
    (args := [⟨.i64, -8⟩, ⟨.i32, 1⟩]) (regs := (Regs.empty.set 0 ⟨.i64, -8⟩).set 1 ⟨.i32, 1⟩)
    (m := Mem.empty) (vals := [⟨.i64, 0x7ffffffffffffffc⟩]) (vals' := [⟨.i64, -4⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

/-- The re-check rejects every certificate for `neg_shAmt`. -/
theorem shAmt_rejected (cert : Cert) :
    checkCert (ConstPhi.run shAmtFn) shAmtWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run shAmtFn) shAmtWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) shAmt_not_sim

def reFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 255 }, { results := [2], inst := .binary .band .i64 0 1 },
    { results := [3], inst := .iconst .i64 15 }, { results := [4], inst := .binary .band .i64 2 3 }] 4
def reWrongGn : Function :=
  fn1 .i64 .i64 [{ results := [5], inst := .iconst .i64 255 },
    { results := [4], inst := .binary .band .i64 0 5 }] 4

theorem reF_text : fn? reF = some reFn := by native_decide
theorem reWrongG_text : fn? reWrongG = some reWrongGn := by native_decide

/-- For `x = 16`: `f` returns 0, `g` 16. -/
theorem re_not_sim : ¬ FunSimMU reFn reWrongGn :=
  not_funSimMU_ret_ne (b := reFn.blocks.head!) (b' := reWrongGn.blocks.head!)
    (args := [⟨.i64, 16⟩]) (regs := Regs.empty.set 0 ⟨.i64, 16⟩) (m := Mem.empty)
    (vals := [⟨.i64, 0⟩]) (vals' := [⟨.i64, 16⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_re`. -/
theorem re_rejected (cert : Cert) : checkCert (ConstPhi.run reFn) reWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run reFn) reWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) re_not_sim

def reShlFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 3 }, { results := [2], inst := .binary .ishl .i64 0 1 },
    { results := [3], inst := .iconst .i64 5 }, { results := [4], inst := .binary .imul .i64 2 3 }] 4
def reShlWrongGn : Function :=
  fn1 .i64 .i64 [{ results := [5], inst := .iconst .i64 15 },
    { results := [4], inst := .binary .imul .i64 0 5 }] 4

theorem reShlF_text : fn? reShlF = some reShlFn := by native_decide
theorem reShlWrongG_text : fn? reShlWrongG = some reShlWrongGn := by native_decide

/-- For `x = 1`: `f` returns 40, `g` 15. -/
theorem reShl_not_sim : ¬ FunSimMU reShlFn reShlWrongGn :=
  not_funSimMU_ret_ne (b := reShlFn.blocks.head!) (b' := reShlWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, 40⟩]) (vals' := [⟨.i64, 15⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_reShl`. -/
theorem reShl_rejected (cert : Cert) :
    checkCert (ConstPhi.run reShlFn) reShlWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run reShlFn) reShlWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) reShl_not_sim

def narrowMaskFn : Function :=
  fn1 .i16 .i8 [{ results := [1], inst := .iconst .i16 127 }, { results := [2], inst := .binary .band .i16 0 1 },
    { results := [3], inst := .ireduce .i8 2 }] 3
def narrowGn : Function := fn1 .i16 .i8 [{ results := [3], inst := .ireduce .i8 0 }] 3

theorem narrowMaskF_text : fn? narrowMaskF = some narrowMaskFn := by native_decide
theorem narrowG_text : fn? narrowG = some narrowGn := by native_decide

/-- For `x = 255`: `f` returns 127, `g` `-1`. -/
theorem narrow_not_sim : ¬ FunSimMU narrowMaskFn narrowGn :=
  not_funSimMU_ret_ne (b := narrowMaskFn.blocks.head!) (b' := narrowGn.blocks.head!)
    (args := [⟨.i16, 255⟩]) (regs := Regs.empty.set 0 ⟨.i16, 255⟩) (m := Mem.empty)
    (vals := [⟨.i8, 127⟩]) (vals' := [⟨.i8, 255⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

/-- The re-check rejects every certificate for `neg_narrow`. -/
theorem narrow_rejected (cert : Cert) :
    checkCert (ConstPhi.run narrowMaskFn) narrowGn cert = false := by
  cases h : checkCert (ConstPhi.run narrowMaskFn) narrowGn cert
  · rfl
  · exact absurd (checked_simMU h) narrow_not_sim

/-! ### The typing premise of `shAmt` is needed -/

def shTms : Array Tm :=
  #[.param 0 0, .param 0 1, .node (.extend .uextend .i128 1), .node (.binary .ushr .i64 0 1)]

theorem shAmt_fires :
    Norm.guard (fam6Step (atomTy Fam4Witness.fn2)) shTms (.binary .ushr .i64 0 2) =
      some (.node (.binary .ushr .i64 0 1)) := by
  native_decide

theorem shAmt_frame :
    tmVal Fam4Witness.fn2 shTms (Fam4Witness.fr2 ⟨.i64, 8⟩ ⟨.i128, 1⟩) Mem.empty 3 ≠
      evalNode (tmFrame Fam4Witness.fn2 shTms (Fam4Witness.fr2 ⟨.i64, 8⟩ ⟨.i128, 1⟩) Mem.empty)
        Mem.empty (.binary .ushr .i64 0 2) := by
  native_decide

/-- `shAmt` is no normaliser sound in every frame (a parameter declared `i64` holding an `i128`:
`uextend.i128` of it has no value, the shift by it has one). -/
theorem shAmt_not_normSound : ¬ NormSound (Norm.guard (fam6Step (atomTy Fam4Witness.fn2))) :=
  fun h => shAmt_frame (h shTms _ _ shAmt_fires Fam4Witness.fn2
    (Fam4Witness.fr2 ⟨.i64, 8⟩ ⟨.i128, 1⟩) Mem.empty 3 rfl)

/-! ## Real pairs

Pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_fam6_*.clif`), each rejected by main's
`checkC` (`checkCPrev`) and accepted by `checkCertC` with the requests `emitC` gives (decided),
with the simulation and the program refinement:

* `amt`: crypto-bigint's `_RNxC13crypto_bigint12HlV9wufij0kF`: `ishl x (ireduce.i32 (clz x))` →
  `ishl x (clz x)` (`shAmt`);
* `mul`: semver's test build, regex_automata's `_RNxC14regex_automata12Ha6ZGqiSITse`: a division
  by 32 times 32 (`ushr` by 5 after `divPre`, then `imul` by 32) → `band x -32` (`fam6Mul`);
* `re`: crypto-bigint's `_RNxC13crypto_bigint12HbNJTzqO4MZX`: `band (ireduce.i8 (band x 1)) 1` →
  `band (ireduce.i8 x) 1` (narrowing, then `reStep`);
* `narrow`: crypto-bigint's ctutils `_RNxC7ctutils12HaFzNS3jBufb`: an `ireduce.i8` of a
  `band` with 255 → `ireduce.i8` (`narrowId`);
* `mulshl`: semver's test build, regex_syntax's `_RNxC12regex_syntax12HjiH6To1FFOY`: `imul
  (ishl x 2) 112` (a division then multiplications) → `imul x 448` (`fam6Mul`, `reStep`).
-/

def amtF : String := include_str "midval/real_fam6_amt.unopt.clif"
def amtG : String := include_str "midval/real_fam6_amt.opt.clif"
def mulF : String := include_str "midval/real_fam6_mul.unopt.clif"
def mulG : String := include_str "midval/real_fam6_mul.opt.clif"
def reF' : String := include_str "midval/real_fam6_re.unopt.clif"
def reG' : String := include_str "midval/real_fam6_re.opt.clif"
def narrowF' : String := include_str "midval/real_fam6_narrow.unopt.clif"
def narrowG' : String := include_str "midval/real_fam6_narrow.opt.clif"
def mulshlF : String := include_str "midval/real_fam6_mulshl.unopt.clif"
def mulshlG : String := include_str "midval/real_fam6_mulshl.opt.clif"

theorem real_amt_prev_rejects : realPrev amtF amtG = some false := by native_decide
theorem real_amt_checked : checkedC amtF amtG = some (true, false) := by native_decide
theorem real_amt_sim : SimRefinesC amtF amtG := simC_of_checked real_amt_checked

theorem real_mul_prev_rejects : realPrev mulF mulG = some false := by native_decide
theorem real_mul_checked : checkedC mulF mulG = some (true, true) := by native_decide
theorem real_mul_sim : SimRefinesC mulF mulG := simC_of_checked real_mul_checked

theorem real_re_prev_rejects : realPrev reF' reG' = some false := by native_decide
theorem real_re_checked : checkedC reF' reG' = some (true, false) := by native_decide
theorem real_re_sim : SimRefinesC reF' reG' := simC_of_checked real_re_checked

theorem real_narrow_prev_rejects : realPrev narrowF' narrowG' = some false := by native_decide
theorem real_narrow_checked : checkedC narrowF' narrowG' = some (true, false) := by native_decide
theorem real_narrow_sim : SimRefinesC narrowF' narrowG' := simC_of_checked real_narrow_checked

theorem real_mulshl_prev_rejects : realPrev mulshlF mulshlG = some false := by native_decide
theorem real_mulshl_checked : checkedC mulshlF mulshlG = some (true, true) := by native_decide
theorem real_mulshl_sim : SimRefinesC mulshlF mulshlG := simC_of_checked real_mulshl_checked

end Opt.MidVal.Fam6Witness
