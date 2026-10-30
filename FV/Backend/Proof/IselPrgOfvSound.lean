import FV.Backend.Proof.IselPrgExt
import FV.Backend.Proof.IselPrgLe
import FV.Backend.Proof.IselFlowSplit

/-!
# Progress of the ISLE lowering (V7): `MInst.ofV` decodes what `ofvOk` accepts

`ofvOk_sound`: every value an abstract value accepted by `ofvOk` describes decodes as an `MInst`
(`emit` never meets an instruction value it cannot decode). Through `minstOk` (one case per
`MInst` variant, plus the loads/stores of `ofV`'s last case), `amodeOk` (`V.amode?`), `condBrOk`
(`V.condBrKind?`) and `enumOk` (`V.enum?`): each accepted field gives its accessor's `some`.

The big matchers are split with `gen_match_split` (`IselFlowSplit`); the decoder is evaluated on
the field shapes by `red_safe`, a step-by-step reduction (each step proved, so that the kernel
never evaluates a stuck discriminant) that stops at the first `if`/`match` stuck on a free
variable, so the field facts rewrite what remains.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

namespace CS

open Lean Meta Elab Tactic

/-- A constructor application or a numeral. -/
def ctorLike (d : Lean.Expr) : MetaM Bool := do
  if d.isRawNatLit then return true
  if d.isAppOfArity ``OfNat.ofNat 3 && (d.getArg! 1).isRawNatLit then return true
  isConstructorApp d

/-- `e = e'` by `rfl`, for a one-step reduct `e'` of `e`. -/
def reflTo (e e' : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e')

/-- One reduction step of `e` with its proof `e = e'`: beta, zeta, a projection of a
constructor, an `if` on a closed decided condition, a discriminant of a `match` to its
constructor, a `match` on constructors (proved once for abstract alternatives, so the kernel never
compares the alternatives' bodies), a definition unfolded. `none`: stuck. -/
def stepEq (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if e.isHeadBetaTarget then
    let e' := e.headBeta
    return some (e', ← reflTo e e')
  match e with
  | .letE _ _ v b _ => let e' := b.instantiate1 v; return some (e', ← reflTo e e')
  | .mdata _ b => return some (b, ← reflTo e b)
  | .proj _ i s =>
    match ← projectCore? (← whnf s) i with
    | some e' => return some (e', ← reflTo e e')
    | none => return none
  | _ => pure ()
  if let .proj _ i s := e.getAppFn then
    match ← projectCore? (← whnf s) i with
    | some h =>
      let e' := mkAppN h e.getAppArgs
      return some (e', ← reflTo e e')
    | none => return none
  for (n, pos, neg) in [(``ite, ``ite_eq_left, ``ite_eq_right),
      (``dite, ``dite_eq_left, ``dite_eq_right)] do
    if e.isAppOfArity n 5 then
      let inst := e.getArg! 2
      if inst.hasFVar || inst.hasMVar then return none
      let instW ← whnf inst
      let c := e.getArg! 1
      if instW.isAppOfArity ``Decidable.isTrue 2 then
        let pf ← mkAppOptM pos #[c, inst, instW.appArg!, e.getArg! 0, e.getArg! 3, e.getArg! 4]
        let some (_, _, e') := (← inferType pf).eq? | return none
        return some (e', pf)
      if instW.isAppOfArity ``Decidable.isFalse 2 then
        let pf ← mkAppOptM neg #[c, inst, instW.appArg!, e.getArg! 0, e.getArg! 3, e.getArg! 4]
        let some (_, _, e') := (← inferType pf).eq? | return none
        return some (e', pf)
      return none
  let fn := e.getAppFn
  let some cn := fn.constName? | return none
  if let some mi ← getMatcherInfo? cn then
    let args := e.getAppArgs
    let d0 := mi.numParams + 1
    let a0 := d0 + mi.numDiscrs
    let alts := args.extract a0 (a0 + mi.numAlts)
    let altTys ← alts.mapM inferType
    let decls := altTys.mapIdx fun j t => (Name.mkSimple s!"alt{j}", fun _ => pure t)
    let res : Option (Lean.Expr × Lean.Expr) ← withLocalDeclsD decls fun xs => do
      let eGen := mkAppN fn (args.extract 0 a0 ++ xs ++ args.extract (a0 + mi.numAlts) args.size)
      match ← reduceMatcher? eGen with
      | .reduced r =>
        let pfGen ← mkLambdaFVars xs (← reflTo eGen r)
        pure (some (r.replaceFVars xs alts, mkAppN pfGen alts))
      | _ => pure none
    if res.isSome then return res
    for i in [d0:a0] do
      let d := args[i]!
      unless ← ctorLike d do
        let d' ← whnf d
        if ← ctorLike d' then
          let e' := mkAppN fn (args.set! i d')
          return some (e', ← reflTo e e')
    return none
  if (← getEnv).isConstructor cn then return none
  match ← unfoldDefinition? e with
  | some e' => return some (e', ← reflTo e e')
  | none => return none

/-- Reduce `e` step by step (`stepEq`), with the proof `e = e'`. -/
partial def redSafe (e pf : Lean.Expr) (fuel : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if fuel = 0 then return (e, pf)
  match ← stepEq e with
  | some (e', p) => redSafe e' (← mkEqTrans pf p) (fuel - 1)
  | none => return (e, pf)

/-- `red_safe c`: reduce (`redSafe`) the first application of the constant `c` in the goal, down
to the first `if` or `match` stuck on a free variable, and rewrite the goal with the proof (single
steps, which the kernel checks without ever reducing a stuck discriminant). -/
elab "red_safe " n:ident : tactic => do
  let c ← realizeGlobalConstNoOverload n
  liftMetaTactic1 fun g => g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some e := t.find? (fun x => x.isAppOf c) | throwError "red_safe: no {c} in the goal"
    let (_, pf) ← redSafe e (← mkEqRefl e) 10000
    let r ← g.rewrite t pf
    g.replaceTargetEq r.eNew r.eqProof


end CS

gen_match_split Backend.Proof.Prg.CS.minstOk_split Backend.Proof.Prg.minstOk.match_6
gen_match_split Backend.Proof.Prg.CS.amodeOk_split Backend.Proof.Prg.amodeOk.match_1
gen_match_split Backend.Proof.Prg.CS.condBrOk_split Backend.Proof.Prg.condBrOk.match_1

variable {f : Clif.Function} {ctx : Ctx}

namespace CS

/-! ## Value lists and field shapes -/

theorem γL_cons {a : PA} {as : List PA} {ws : List V} (h : γL f ctx (a :: as) ws) :
    ∃ w ws', ws = w :: ws' ∧ γ f ctx a w ∧ γL f ctx as ws' := γL_cons_iff.1 h

theorem γL_nil {ws : List V} (h : γL f ctx [] ws) : ws = [] := γL_nil_iff.1 h

theorem reg_sh {a : PA} {w : V} (h : isReg a = true) (hw : γ f ctx a w) : ∃ r, w = .reg r := by
  cases a with
  | reg => simpa only [γ] using hw
  | bot => simp [γ] at hw
  | _ => simp [isReg] at h

theorem label_sh {a : PA} {w : V} (h : isLabel a = true) (hw : γ f ctx a w) :
    ∃ l, w = .label l := by
  cases a with
  | label => simpa only [γ] using hw
  | bot => simp [γ] at hw
  | _ => simp [isLabel] at h

theorem bool_sh {a : PA} {w : V} (h : isBool a = true) (hw : γ f ctx a w) : ∃ b, w = .bool b := by
  cases a with
  | bool c => simp only [γ] at hw; obtain ⟨x, rfl, -⟩ := hw; exact ⟨x, rfl⟩
  | bot => simp [γ] at hw
  | _ => simp [isBool] at h

theorem int_sh {a : PA} {w : V} (h : isInt a = true) (hw : γ f ctx a w) : ∃ i, w = .int i := by
  cases a with
  | int lo hi => simp only [γ] at hw; obtain ⟨x, rfl, -⟩ := hw; exact ⟨x, rfl⟩
  | bot => simp [γ] at hw
  | _ => simp [isInt] at h

theorem ty_sh {a : PA} {w : V} (h : isTy a = true) (hw : γ f ctx a w) :
    ∃ ts t, a = .ty ts ∧ t ∈ ts ∧ w = .ty t := by
  cases a with
  | ty ts => simp only [γ] at hw; obtain ⟨t, ht, rfl⟩ := hw; exact ⟨ts, t, rfl, ht, rfl⟩
  | bot => simp [γ] at hw
  | _ => simp [isTy] at h

theorem nat_sh {a : PA} {w : V} (h : isNat a = true) (hw : γ f ctx a w) :
    ∃ i, w = .int i ∧ 0 ≤ i := by
  cases a with
  | int lo hi =>
    cases lo with
    | none => simp [isNat] at h
    | some l =>
      simp only [isNat, decide_eq_true_eq] at h
      simp only [γ] at hw
      obtain ⟨i, rfl, hl, -⟩ := hw
      exact ⟨i, rfl, Int.le_trans h (hl l rfl)⟩
  | bot => simp [γ] at hw
  | _ => simp [isNat] at h

theorem op_sh {k : OK} {a : PA} {w : V} (h : isOp k a = true) (hw : γ f ctx a w) :
    ∃ o n, w = .op o ∧ OpOk ctx k n o := by
  cases a with
  | op k' n =>
    simp only [isOp, beq_iff_eq] at h
    subst h
    simp only [γ] at hw
    obtain ⟨o, rfl, ho⟩ := hw
    exact ⟨o, n, rfl, ho⟩
  | bot => simp [γ] at hw
  | _ => simp [isOp] at h

theorem simm9_sh {n : Option Nat} {w : V} (hw : γ f ctx (.op .simm9 n) w) :
    ∃ i, w = .op (.simm9 i) := by
  simp only [γ] at hw
  obtain ⟨o, rfl, i, rfl⟩ := hw
  exact ⟨i, rfl⟩

theorem uimm12Scaled_sh {n : Option Nat} {w : V} (hw : γ f ctx (.op .uimm12Scaled n) w) :
    ∃ i, w = .op (.uimm12Scaled i) := by
  simp only [γ] at hw
  obtain ⟨o, rfl, i, rfl⟩ := hw
  exact ⟨i, rfl⟩

/-! ## Accessors -/

theorem reg_acc {a : PA} {w : V} (h : isReg a = true) (hw : γ f ctx a w) :
    ∃ r, w.reg? = some r := by
  obtain ⟨r, rfl⟩ := reg_sh h hw; exact ⟨r, rfl⟩

theorem label_acc {a : PA} {w : V} (h : isLabel a = true) (hw : γ f ctx a w) :
    ∃ l, w.label? = some l := by
  obtain ⟨l, rfl⟩ := label_sh h hw; exact ⟨l, rfl⟩

theorem bool_acc {a : PA} {w : V} (h : isBool a = true) (hw : γ f ctx a w) :
    ∃ b, w.bool? = some b := by
  obtain ⟨b, rfl⟩ := bool_sh h hw; exact ⟨b, rfl⟩

theorem int_acc {a : PA} {w : V} (h : isInt a = true) (hw : γ f ctx a w) :
    ∃ i, w.int? = some i := by
  obtain ⟨i, rfl⟩ := int_sh h hw; exact ⟨i, rfl⟩

theorem ty_acc {a : PA} {w : V} (h : isTy a = true) (hw : γ f ctx a w) : ∃ t, w.ty? = some t := by
  obtain ⟨_, t, -, -, rfl⟩ := ty_sh h hw; exact ⟨t, rfl⟩

theorem nat_acc {a : PA} {w : V} (h : isNat a = true) (hw : γ f ctx a w) :
    ∃ n, w.nat? = some n := by
  obtain ⟨i, rfl, hi⟩ := nat_sh h hw; exact ⟨i.toNat, by simp [V.nat?, hi]⟩

theorem labelsM_acc {a : PA} {w : V} (h : (match a with | .labels _ _ => true | _ => false) = true)
    (hw : γ f ctx a w) : ∃ ls, w.labels? = some ls := by
  cases a with
  | labels lo n => simp only [γ] at hw; obtain ⟨ls, rfl, -⟩ := hw; exact ⟨ls, rfl⟩
  | _ => simp at h

theorem op_imm12_acc {a : PA} {w : V} (h : isOp .imm12 a = true) (hw : γ f ctx a w) :
    ∃ x, w.imm12? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_immLogic_acc {a : PA} {w : V} (h : isOp .immLogic a = true) (hw : γ f ctx a w) :
    ∃ x, w.immLogic? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_immShift_acc {a : PA} {w : V} (h : isOp .immShift a = true) (hw : γ f ctx a w) :
    ∃ x, w.immShift? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl, -⟩ := ho
  exact ⟨x, rfl⟩

theorem op_shiftAmt_acc {a : PA} {w : V} (h : isOp .shiftAmt a = true) (hw : γ f ctx a w) :
    ∃ x, w.shiftOpAndAmt? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_mwc_acc {a : PA} {w : V} (h : isOp .mwc a = true) (hw : γ f ctx a w) :
    ∃ x, w.moveWideConst? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_uimm6_acc {a : PA} {w : V} (h : isOp .uimm6 a = true) (hw : γ f ctx a w) :
    ∃ x, w.uimm6? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_nzcv_acc {a : PA} {w : V} (h : isOp .nzcv a = true) (hw : γ f ctx a w) :
    ∃ x, w.nzcv? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_uimm5_acc {a : PA} {w : V} (h : isOp .uimm5 a = true) (hw : γ f ctx a w) :
    ∃ x, w.uimm5? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_callInfo_acc {a : PA} {w : V} (h : isOp .callInfo a = true) (hw : γ f ctx a w) :
    ∃ x, w.callInfo? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_trapCode_acc {a : PA} {w : V} (h : isOp .trapCode a = true) (hw : γ f ctx a w) :
    ∃ x, w.trapCode? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_extName_acc {a : PA} {w : V} (h : isOp .extName a = true) (hw : γ f ctx a w) :
    ∃ x, w.extName? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_memFlags_acc {a : PA} {w : V} (h : isOp .memFlags a = true) (hw : γ f ctx a w) :
    ∃ x, w.memFlags? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl, -⟩ := ho
  exact ⟨x, rfl⟩

/-! ## Enum values -/

mutual
/-- An enum value of a type whose variants `enumsOf` lists. -/
theorem enumsOf_sound {ty : TypeId} : ∀ {a : PA} {ks : List Nat} {w : V},
    PA.enumsOf ty a = some ks → γ f ctx a w → ∃ k ∈ ks, w = .data ty k []
  | .bot, _, _, _, hw => by simp [γ] at hw
  | .data t k fs, ks, w, h, hw => by
    simp only [PA.enumsOf] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [γ] at hw
      obtain ⟨ws, rfl, hws⟩ := hw
      rw [γL_nil hws]
      exact ⟨k, List.mem_singleton_self k, rfl⟩
    · cases h
  | .alts as, ks, w, h, hw => by
    simp only [PA.enumsOf] at h
    simp only [γ] at hw
    exact enumsOfL_sound h hw
  | .any, _, _, h, _
  | .int _ _, _, _, h, _
  | .bool _, _, _, h, _
  | .ty _, _, _, h, _
  | .inst _ _, _, _, h, _
  | .val _, _, _, h, _
  | .vals _, _, _, h, _
  | .valsMin _, _, _, h, _
  | .reg, _, _, h, _
  | .regs _, _, _, h, _
  | .regsVec _, _, _, h, _
  | .label, _, _, h, _
  | .labels _ _, _, _, h, _
  | .blockCalls _, _, _, h, _
  | .idata, _, _, h, _
  | .op _ _, _, _, h, _ => by simp [PA.enumsOf] at h
/-- `enumsOf_sound` for alternatives. -/
theorem enumsOfL_sound {ty : TypeId} : ∀ {as : List PA} {ks : List Nat} {w : V},
    PA.enumsOfL ty as = some ks → γAny f ctx as w → ∃ k ∈ ks, w = .data ty k []
  | [], _, _, _, hw => by simp [γAny] at hw
  | a :: as, ks, w, h, hw => by
    simp only [PA.enumsOfL, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    simp only [γAny] at hw
    rcases hw with hw | hw
    · obtain ⟨k, hk, rfl⟩ := enumsOf_sound hx hw
      exact ⟨k, List.mem_append_left _ hk, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := enumsOfL_sound hy hw
      exact ⟨k, List.mem_append_right _ hk, rfl⟩
end

theorem enum_sh {α : Type} {ty : TypeId} {g : Nat → Option α} {a : PA} {w : V}
    (h : enumOk ty g a = true) (hw : γ f ctx a w) : ∃ k x, w = .data ty k [] ∧ g k = some x := by
  unfold enumOk at h
  cases he : a.enumsOf ty with
  | none => simp [he] at h
  | some ks =>
    simp only [he, List.all_eq_true] at h
    obtain ⟨k, hk, rfl⟩ := enumsOf_sound he hw
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (h k hk)
    exact ⟨k, x, rfl, hx⟩

theorem enum_acc {α : Type} {ty : TypeId} {g : Nat → Option α} {a : PA} {w : V}
    (h : enumOk ty g a = true) (hw : γ f ctx a w) (acc : V → Option α)
    (hacc : ∀ v, acc v = V.enum? ty g v) : ∃ x, acc w = some x := by
  obtain ⟨k, x, rfl, hx⟩ := enum_sh h hw
  exact ⟨x, by rw [hacc]; simp [V.enum?, V.enumOf?, hx]⟩

end CS

mutual
/-- **`amodeOk` is sound.** -/
theorem amodeOk_sound : ∀ {a : PA} {w : V}, amodeOk a = true → γ f ctx a w →
    (w.amode?).isSome = true
  | .bot, _, _, hw => by simp [γ] at hw
  | .alts as, w, h, hw => by
    simp only [amodeOk] at h
    simp only [γ] at hw
    exact amodeOkL_sound h hw
  | .data t k fs, w, h, hw => by
    simp only [amodeOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [γ] at hw
    obtain ⟨ws, rfl, hws⟩ := hw
    revert ws
    revert hm
    apply CS.amodeOk_split _ (fun k fs r => r = true → ∀ ws, γL f ctx fs ws →
      ((V.data tyAMode k ws).amode?).isSome = true)
    -- RegReg
    · intro p1 p2 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
      red_safe V.amode?
      simp only [e1, e2] <;> rfl
    -- RegScaled
    · intro p1 p2 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
      red_safe V.amode?
      simp only [e1, e2] <;> rfl
    -- RegScaledExtended
    · intro p1 p2 p3 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
      obtain ⟨_, e3⟩ := CS.enum_acc h3 hw3 V.extendOp? (fun _ => rfl)
      red_safe V.amode?
      simp only [e1, e2, e3] <;> rfl
    -- RegExtended
    · intro p1 p2 p3 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
      obtain ⟨_, e3⟩ := CS.enum_acc h3 hw3 V.extendOp? (fun _ => rfl)
      red_safe V.amode?
      simp only [e1, e2, e3] <;> rfl
    -- Unscaled
    · intro p1 p2 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, rfl⟩ := CS.simm9_sh hw2
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- UnsignedOffset
    · intro p1 p2 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, rfl⟩ := CS.uimm12Scaled_sh hw2
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- RegOffset
    · intro p1 p2 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.int_acc h2 hw2
      red_safe V.amode?
      simp only [e1, e2] <;> rfl
    -- SPOffset
    · intro p1 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.int_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- FPOffset
    · intro p1 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.int_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- IncomingArg
    · intro p1 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.int_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- SlotOffset
    · intro p1 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.int_acc h1 hw1
      red_safe V.amode?
      simp only [e1] <;> rfl
    -- SPPreIndexed
    · intro p1 h ws hws
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, rfl⟩ := CS.simm9_sh hw1
      red_safe V.amode?
      rfl
    -- SPPostIndexed
    · intro p1 h ws hws
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, rfl⟩ := CS.simm9_sh hw1
      red_safe V.amode?
      rfl
    · intro _ _ h; cases h
  | .any, _, h, _
  | .int _ _, _, h, _
  | .bool _, _, h, _
  | .ty _, _, h, _
  | .inst _ _, _, h, _
  | .val _, _, h, _
  | .vals _, _, h, _
  | .valsMin _, _, h, _
  | .reg, _, h, _
  | .regs _, _, h, _
  | .regsVec _, _, h, _
  | .label, _, h, _
  | .labels _ _, _, h, _
  | .blockCalls _, _, h, _
  | .idata, _, h, _
  | .op _ _, _, h, _ => by simp [amodeOk] at h
/-- `amodeOk_sound` for alternatives. -/
theorem amodeOkL_sound : ∀ {as : List PA} {w : V}, amodeOkL as = true → γAny f ctx as w →
    (w.amode?).isSome = true
  | [], _, _, hw => by simp [γAny] at hw
  | a :: as, w, h, hw => by
    simp only [amodeOkL, Bool.and_eq_true] at h
    simp only [γAny] at hw
    rcases hw with hw | hw
    · exact amodeOk_sound h.1 hw
    · exact amodeOkL_sound h.2 hw
end

theorem amodeOk_acc {a : PA} {w : V} (h : amodeOk a = true) (hw : γ f ctx a w) :
    ∃ m, w.amode? = some m := Option.isSome_iff_exists.1 (amodeOk_sound h hw)

mutual
/-- **`condBrOk` is sound.** -/
theorem condBrOk_sound : ∀ {a : PA} {w : V}, condBrOk a = true → γ f ctx a w →
    (w.condBrKind?).isSome = true
  | .bot, _, _, hw => by simp [γ] at hw
  | .alts as, w, h, hw => by
    simp only [condBrOk] at h
    simp only [γ] at hw
    exact condBrOkL_sound h hw
  | .data t k fs, w, h, hw => by
    simp only [condBrOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [γ] at hw
    obtain ⟨ws, rfl, hws⟩ := hw
    revert ws
    revert hm
    apply CS.condBrOk_split _ (fun k fs r => r = true → ∀ ws, γL f ctx fs ws →
      ((V.data tyCondBrKind k ws).condBrKind?).isSome = true)
    -- Zero
    · intro p1 p2 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
      red_safe V.condBrKind?
      simp only [e1, e2] <;> rfl
    -- NotZero
    · intro p1 p2 h ws hws
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
      obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
      red_safe V.condBrKind?
      simp only [e1, e2] <;> rfl
    -- Cond
    · intro p1 h ws hws
      have h1 := h
      obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
      obtain rfl := CS.γL_nil hws
      obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.cond? (fun _ => rfl)
      red_safe V.condBrKind?
      simp only [e1] <;> rfl
    · intro _ _ h; cases h
  | .any, _, h, _
  | .int _ _, _, h, _
  | .bool _, _, h, _
  | .ty _, _, h, _
  | .inst _ _, _, h, _
  | .val _, _, h, _
  | .vals _, _, h, _
  | .valsMin _, _, h, _
  | .reg, _, h, _
  | .regs _, _, h, _
  | .regsVec _, _, h, _
  | .label, _, h, _
  | .labels _ _, _, h, _
  | .blockCalls _, _, h, _
  | .idata, _, h, _
  | .op _ _, _, h, _ => by simp [condBrOk] at h
/-- `condBrOk_sound` for alternatives. -/
theorem condBrOkL_sound : ∀ {as : List PA} {w : V}, condBrOkL as = true → γAny f ctx as w →
    (w.condBrKind?).isSome = true
  | [], _, _, hw => by simp [γAny] at hw
  | a :: as, w, h, hw => by
    simp only [condBrOkL, Bool.and_eq_true] at h
    simp only [γAny] at hw
    rcases hw with hw | hw
    · exact condBrOk_sound h.1 hw
    · exact condBrOkL_sound h.2 hw
end

theorem condBrOk_acc {a : PA} {w : V} (h : condBrOk a = true) (hw : γ f ctx a w) :
    ∃ c, w.condBrKind? = some c := Option.isSome_iff_exists.1 (condBrOk_sound h hw)

/-- The variant indices of the loads and stores `ofV`'s last case decodes. -/
theorem CS.loadStore_idx {k : Nat}
    (h : (loadOpOfIdx? k).isSome = true ∨ (storeOpOfIdx? k).isSome = true) :
    k = VIdx.MInst.ULoad8 ∨ k = VIdx.MInst.SLoad8 ∨ k = VIdx.MInst.ULoad16 ∨
      k = VIdx.MInst.SLoad16 ∨ k = VIdx.MInst.ULoad32 ∨ k = VIdx.MInst.SLoad32 ∨
      k = VIdx.MInst.ULoad64 ∨ k = VIdx.MInst.Store8 ∨ k = VIdx.MInst.Store16 ∨
      k = VIdx.MInst.Store32 ∨ k = VIdx.MInst.Store64 := by
  rcases h with h | h
  · unfold loadOpOfIdx? at h; split at h <;> simp_all
  · unfold storeOpOfIdx? at h; split at h <;> simp_all

/-- **`minstOk` is sound**: `MInst.ofV` decodes every value of variant `k` with fields `fs`
describe. -/
theorem minstOk_sound {k : Nat} {fs : List PA} (h : minstOk k fs = true) {ws : List V}
    (hws : γL f ctx fs ws) : (MInst.ofV (.data tyMInst k ws)).isSome = true := by
  revert ws
  revert h
  unfold minstOk
  apply CS.minstOk_split _ (fun k fs r => r = true → ∀ ws, γL f ctx fs ws →
    (MInst.ofV (.data tyMInst k ws)).isSome = true)
  -- AluRRR
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- AluRRRR
  · intro p1 p2 p3 p4 p5 p6 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp3? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.reg_acc h6 hw6
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6] <;> rfl
  -- AluRRImm12
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.op_imm12_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- AluRRImmLogic
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.op_immLogic_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- AluRRImmShift
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.op_immShift_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- AluRRRShift
  · intro p1 p2 p3 p4 p5 p6 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.op_shiftAmt_acc h6 hw6
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6] <;> rfl
  -- AluRRRExtend
  · intro p1 p2 p3 p4 p5 p6 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.aluOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.enum_acc h6 hw6 V.extendOp? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6] <;> rfl
  -- BitRR
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.bitOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.size? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- Mov
  · intro p1 p2 p3 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.size? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- MovWide
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.moveWideOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.op_mwc_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.size? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- MovK
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.op_mwc_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.size? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- Extend
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.bool_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.nat_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.nat_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- BitfieldMove
  · intro p1 p2 p3 p4 p5 p6 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.size? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.bfmOp? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.op_uimm6_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.op_uimm6_acc h6 hw6
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6] <;> rfl
  -- CSet
  · intro p1 p2 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.cond? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2] <;> rfl
  -- CSel
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.cond? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- CCmp
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.size? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.op_nzcv_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.enum_acc h5 hw5 V.cond? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- CCmpImm
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.size? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.op_uimm5_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.op_nzcv_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.enum_acc h5 hw5 V.cond? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- MovToFpu
  · intro p1 p2 p3 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.enum_acc h3 hw3 V.scalarSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- MovFromVec
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.nat_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.scalarSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- VecMisc
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.vecMisc2? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.vectorSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- VecLanes
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.vecLanesOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.vectorSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- VecRRR
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.vecALUOp? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.enum_acc h5 hw5 V.vectorSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- Call
  · intro p1 h ws hws
    have h1 := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.op_callInfo_acc h1 hw1
    red_safe MInst.ofV
    simp only [e1] <;> rfl
  -- CallInd
  · intro p1 h ws hws
    have h1 := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.op_callInfo_acc h1 hw1
    red_safe MInst.ofV
    simp only [e1] <;> rfl
  -- Jump
  · intro p1 h ws hws
    have h1 := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.label_acc h1 hw1
    red_safe MInst.ofV
    simp only [e1] <;> rfl
  -- CondBr
  · intro p1 p2 p3 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.label_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.label_acc h2 hw2
    obtain ⟨_, e3⟩ := condBrOk_acc h3 hw3
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- TestBitAndBranch
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.tbKind? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.label_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.label_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.nat_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- TrapIf
  · intro p1 p2 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := condBrOk_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_trapCode_acc h2 hw2
    red_safe MInst.ofV
    simp only [e1, e2] <;> rfl
  -- Udf
  · intro p1 h ws hws
    have h1 := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.op_trapCode_acc h1 hw1
    red_safe MInst.ofV
    simp only [e1] <;> rfl
  -- JTSequence
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.label_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.labelsM_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- LoadExtNameGot
  · intro p1 p2 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_extName_acc h2 hw2
    red_safe MInst.ofV
    simp only [e1, e2] <;> rfl
  -- LoadExtNameNear
  · intro p1 p2 p3 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_extName_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.int_acc h3 hw3
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- LoadAddr
  · intro p1 p2 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := amodeOk_acc h2 hw2
    red_safe MInst.ofV
    simp only [e1, e2] <;> rfl
  -- EmitIsland
  · intro p1 h ws hws
    have h1 := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.nat_acc h1 hw1
    red_safe MInst.ofV
    simp only [e1] <;> rfl
  -- LoadAcquire
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.ty_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.op_memFlags_acc h4 hw4
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- StoreRelease
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.ty_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.op_memFlags_acc h4 hw4
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- AtomicRMWLoop
  · intro p1 p2 p3 p4 p5 p6 p7 p8 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain ⟨w7, ws, rfl, hw7, hws⟩ := CS.γL_cons hws
    obtain ⟨w8, ws, rfl, hw8, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.ty_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.atomicRmwLoopOp? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.op_memFlags_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.reg_acc h6 hw6
    obtain ⟨_, e7⟩ := CS.reg_acc h7 hw7
    obtain ⟨_, e8⟩ := CS.reg_acc h8 hw8
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6, e7, e8] <;> rfl
  -- AtomicCASLoop
  · intro p1 p2 p3 p4 p5 p6 p7 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain ⟨w7, ws, rfl, hw7, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.ty_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_memFlags_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.reg_acc h6 hw6
    obtain ⟨_, e7⟩ := CS.reg_acc h7 hw7
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6, e7] <;> rfl
  -- CSetm
  · intro p1 p2 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.cond? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2] <;> rfl
  -- Fence
  · intro _ h ws hws
    obtain rfl := CS.γL_nil hws
    red_safe MInst.ofV
    rfl
  -- ElfTlsGetAddr
  · intro p1 p2 p3 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.op_extName_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- loads and stores (`ofV`'s last case)
  · intro k p1 p2 p3 h ws hws
    obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
    obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
    obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    have key : (isReg p1 && amodeOk p2 && isOp .memFlags p3) = true ∧
        ((loadOpOfIdx? k).isSome = true ∨ (storeOpOfIdx? k).isSome = true) := by
      revert h
      cases loadOpOfIdx? k <;> cases storeOpOfIdx? k <;> simp
    obtain ⟨h, hk⟩ := key
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := amodeOk_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.op_memFlags_acc h3 hw3
    rcases CS.loadStore_idx hk with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (red_safe MInst.ofV; simp only [e1, e2, e3] <;> rfl)
  · intro _ _ h; cases h

mutual
/-- `ofvOk_sound`, by recursion on the abstract value. -/
theorem ofvOk_sound' : ∀ {a : PA} {v : V}, ofvOk a = true → γ f ctx a v →
    (MInst.ofV v).isSome = true
  | .bot, _, _, hv => by simp [γ] at hv
  | .alts as, v, h, hv => by
    simp only [ofvOk] at h
    simp only [γ] at hv
    exact ofvOkL_sound' h hv
  | .data t k fs, v, h, hv => by
    simp only [ofvOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [γ] at hv
    obtain ⟨ws, rfl, hws⟩ := hv
    exact minstOk_sound hm hws
  | .any, _, h, _
  | .int _ _, _, h, _
  | .bool _, _, h, _
  | .ty _, _, h, _
  | .inst _ _, _, h, _
  | .val _, _, h, _
  | .vals _, _, h, _
  | .valsMin _, _, h, _
  | .reg, _, h, _
  | .regs _, _, h, _
  | .regsVec _, _, h, _
  | .label, _, h, _
  | .labels _ _, _, h, _
  | .blockCalls _, _, h, _
  | .idata, _, h, _
  | .op _ _, _, h, _ => by simp [ofvOk] at h
/-- `ofvOk_sound'` for alternatives. -/
theorem ofvOkL_sound' : ∀ {as : List PA} {v : V}, ofvOkL as = true → γAny f ctx as v →
    (MInst.ofV v).isSome = true
  | [], _, _, hv => by simp [γAny] at hv
  | a :: as, v, h, hv => by
    simp only [ofvOkL, Bool.and_eq_true] at h
    simp only [γAny] at hv
    rcases hv with hv | hv
    · exact ofvOk_sound' h.1 hv
    · exact ofvOkL_sound' h.2 hv
end

/-- **`emit` decodes every instruction value `ofvOk` accepts**: an abstract value `ofvOk`
accepts describes only values `MInst.ofV` decodes. -/
theorem ofvOk_sound {a : PA} {v : V} (h : ofvOk a = true) (hv : γ f ctx a v) :
    (MInst.ofV v).isSome := ofvOk_sound' h hv

end Backend.Proof.Prg
