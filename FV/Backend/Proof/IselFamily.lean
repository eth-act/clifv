import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselRules

/-!
# Batching template: root rules of `lower` from "the rule matched"

`LowerRuleOk` starts from a successful match of the root rule on `[.inst ii]`. The steps that
are the same for every root rule are proved once here:

1. **Which instruction** (`root_match_data`): every one of the 129 closure root rules has the
   argument pattern `(inst_data_value tyPat (InstructionData.K (Opcode.O …) …))`, so a
   successful match fixes the instruction's `InstructionData` format and opcode
   (`IselGeneric`'s match inversion). `CtxInv.data` says the data is `instData f inst`, and
   `instData_names` / `instNames` invert `instData` back to the CLIF instruction.
2. **Determinism**: the rule's forward lemmas (match and right-hand side, `isel_eval`, as in the
   probe) compute the environment, the emitted instructions and the result registers.
3. **Meaning** (`seqRun_alu`): running the emitted `MInst` under any `isem` that refines
   `ispec`, and the width lemmas (`VHolds`).

`aluRR_ruleOk` packages 1–3 for the two-register ALU rules (`iadd_base_case`,
`isub_base_case`, …): a rule of that family is proved by its two forward lemmas and one
width lemma per operation.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## 1. Which instruction matched -/

theorem sem_unData_inv {ctx : Ctx} {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  cases v <;> simp [sem] at h
  rename_i t k' fs'
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem matchArgs_nil_inv {p : Program} {sem' : Isle.Sem V LState} {st : LState} {ws : List V}
    {env env' : Interp.Env V} (h : matchArgs p sem' st [] ws env = .ok (some env')) : ws = [] := by
  cases ws with
  | nil => rfl
  | cons w ws => unfold matchArgs at h; cases h

theorem matchArgs_cons_nil {p : Program} {sem' : Isle.Sem V LState} {st : LState} {q : Pattern}
    {qs : List Pattern} {env env' : Interp.Env V}
    (h : matchArgs p sem' st (q :: qs) [] env = .ok (some env')) : False := by
  unfold matchArgs at h; cases h

theorem ext_inst_data_value_inv {ctx : Ctx} {ii : Nat} {st : LState} {fs : List V}
    (h : externExtract ctx T.inst_data_value (.inst ii) st = .ok fs) :
    ∃ info, ctx.insts[ii]? = some info ∧ fs = [.ty (info.resTys.head?.getD .invalid), info.data] := by
  have e : externExtract ctx T.inst_data_value (.inst ii) st = match ctx.insts[ii]? with
    | some info => .ok [.ty (info.resTys.head?.getD .invalid), info.data]
    | none => .unmodeled s!"inst {ii}" := rfl
  rw [e] at h
  cases hi : ctx.insts[ii]? with
  | none => rw [hi] at h; cases h
  | some info => rw [hi] at h; cases h; exact ⟨info, rfl, rfl⟩

/-- **The instruction a root rule matched**: its `InstructionData` has the format and opcode
the rule's pattern names. -/
theorem root_match_data {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} {m : Nat}
    {r : Rule} {ii : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    {tyPat : Pattern} {fmtT opT : TermId} {rest : List Pattern} {tf to : Term} {kf ko : Nat}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 fmtT (.term 151 opT [] :: rest)]])
    (htf : termOf p fmtT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ info fs, ctx.insts[ii]? = some info ∧ info.data = .data 152 kf (.data 151 ko [] :: fs) := by
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
  rw [hargs] at ha
  obtain ⟨e1, hp1, -⟩ := matchArgs_cons_inv ha
  obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl hp1
  rw [sem_extract] at hx
  obtain ⟨info, hi, rfl⟩ := ext_inst_data_value_inv hx
  obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
  obtain ⟨e3, hp3, -⟩ := matchArgs_cons_inv hm2
  obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv htf hkf hp3
  have hd := sem_unData_inv hu
  cases fs' with
  | nil => exact (matchArgs_cons_nil hm3).elim
  | cons w ws =>
    obtain ⟨e4, hp4, -⟩ := matchArgs_cons_inv hm3
    obtain ⟨fs'', hu', hm4⟩ := matchPat_enum_inv hto hko hp4
    have hw := sem_unData_inv hu'
    have := matchArgs_nil_inv hm4
    subst this
    exact ⟨info, ws, hi, by rw [hd, hw]⟩

/-! ### Inverting `instData` -/

/-- The `InstructionData` format and opcode *names* `instData` uses for an instruction. -/
def instNames : Clif.Inst → String × String
  | .iconst .. => ("UnaryImm", "Iconst")
  | .unary op .. => ("Unary", (unaryOpcode op).getD "")
  | .binary op .. => ("Binary", (binaryOpcode op).getD "")
  | .div op .. => ("Binary", divOpcode op)
  | .icmp .. => ("IntCompare", "Icmp")
  | .extend op .. => ("Unary", if op == .uextend then "Uextend" else "Sextend")
  | .ireduce .. => ("Unary", "Ireduce")
  | .load op .. => ("Load", loadOpcode op)
  | .store op .. => ("Store", storeOpcode op)
  | .select .. => ("Ternary", "Select")
  | .nop => ("NullAry", "Nop")
  | .symbolValue .. => ("UnaryGlobalValue", "SymbolValue")
  | .stackAddr .. => ("StackAddr", "StackAddr")
  | .call .. => ("Call", "Call")
  | .callIndirect .. => ("CallIndirect", "CallIndirect")
  | .funcAddr .. => ("FuncAddr", "FuncAddr")
  -- `bmask`, the atomics and `fence` (agent/atomics-proof)
  | .bmask .. => ("Unary", "Bmask")
  | .atomicLoad .. => ("LoadNoOffset", "AtomicLoad")
  | .atomicStore .. => ("StoreNoOffset", "AtomicStore")
  | .atomicRmw .. => ("AtomicRmw", "AtomicRmw")
  | .atomicCas .. => ("AtomicCas", "AtomicCas")
  | .fence => ("NullAry", "Fence")
  -- agent/fv-lcheck-tls: `tls_value` (unverified, outside `E2E.InSubset`)
  | .tlsValue .. => ("UnaryGlobalValue", "TlsValue")
  | _ => ("", "")

set_option maxRecDepth 20000 in
/-- `instData` builds the data of its format and opcode names. -/
theorem instData_names {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    ∃ rest, d = instDataV (instNames c).1 (opcodeV (instNames c).2 :: rest) := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       simp only [instNames, Option.getD_some, *]
       exact ⟨_, rfl⟩)

theorem mkVariant_eq_data {ty : TypeId} {n : String} {fs : List V} {t k : Nat} {fs' : List V}
    (h : mkVariant ty n fs = .data t k fs') : (variantNames ty)[k]? = some n ∧ t = ty ∧ fs' = fs := by
  unfold mkVariant variantIdx at h
  cases hk : List.idxOf? n (variantNames ty) with
  | none => rw [hk] at h; cases h
  | some k' =>
    rw [hk] at h
    injection h with h1 h2 h3
    subst h1 h2 h3
    obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.mp hk
    exact ⟨by rw [List.getElem?_eq_getElem hlt, hget], rfl, rfl⟩

/-- The names of the instruction whose data has format `kf` and opcode `ko`. -/
theorem instData_inv_names {f : Clif.Function} {c : Clif.Inst} {kf ko : Nat} {fs : List V}
    (h : instData f c = .ok (.data 152 kf (.data 151 ko [] :: fs))) :
    (variantNames 152)[kf]? = some (instNames c).1 ∧ (variantNames 151)[ko]? = some (instNames c).2 := by
  obtain ⟨rest, hd⟩ := instData_names h
  obtain ⟨h1, -, h3⟩ := mkVariant_eq_data hd.symm
  injection h3 with h4 _
  obtain ⟨h5, -, -⟩ := mkVariant_eq_data h4.symm
  exact ⟨h1, h5⟩

theorem binaryOpcode_inj {a b : Clif.BinaryOp} {n : String} (ha : binaryOpcode a = some n)
    (hb : binaryOpcode b = some n) : a = b := by
  cases a <;> cases b <;> simp [binaryOpcode] at ha hb <;> subst ha <;> first | rfl | simp at hb

/-- A two-register instruction with opcode name `n` (the name of `cop`) is `cop`. -/
theorem instNames_binary {c : Clif.Inst} {cop : Clif.BinaryOp} {n : String}
    (hcop : binaryOpcode cop = some n) (h : instNames c = ("Binary", n)) :
    ∃ ty x y, c = .binary cop ty x y := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h <;> simp at h
  case binary op ty x y =>
    have : binaryOpcode op = some n := by
      cases hb : binaryOpcode op with
      | none => rw [hb] at h; simp at h; subst h; cases cop <;> simp [binaryOpcode] at hcop
      | some m => rw [hb] at h; simp at h; rw [h]
    exact ⟨ty, x, y, by rw [binaryOpcode_inj this hcop]⟩
  case div op ty x y =>
    exfalso; cases op <;> cases cop <;> simp [divOpcode, binaryOpcode] at h hcop <;> subst hcop <;>
      simp at h

/-! ## 3. Meaning of the emitted code -/

theorem getAs_ok {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {u : BitVec ty.width}
    (h : fr.getAs x ty = .ok u) : fr.regs x = some ⟨ty, u⟩ := by
  unfold Clif.Frame.getAs Clif.Frame.get at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some v =>
    rw [hx] at h
    obtain ⟨vty, vb⟩ := v
    by_cases hty : vty = ty
    · subst hty
      simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Val.as?] at h
      rw [h]
    · simp [Clif.Res.ofOption, bind, Clif.Res.bind, Clif.Val.as?, hty] at h

/-- The operands of a register-register ALU instruction over vregs. -/
theorem operands_aluRRR (op : ALUOp) (sz : OperandSize) (d x y : Nat) :
    (MInst.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
        ⟨y, .int, .use, .early, .reg⟩] := rfl

theorem ispec_aluRRR {op : ALUOp} {sz : OperandSize} {d : Nat} {rn rm : Reg} {a b : CV}
    {w : Arm.ArmState} {r : BitVec sz.bits} (hv : aluVal op (opnd sz a) (opnd sz b) = some r) :
    ispec (.aluRRR op sz (.vreg d .int) rn rm) [a, b] w = some ([resX sz r], w, .next) := by
  cases op <;> simp [aluVal] at hv <;> subst hv <;> rfl

/-- **One register-register ALU instruction**, run under any `isem` refining `ispec`: vreg `d`
gets the result, every other vreg is unchanged, the world stays the same outside the
allocatable registers. -/
theorem seqRun_aluRRR {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {op : ALUOp}
    {sz : OperandSize} {d x y : Nat} {ρ : Nat → CV} {w : Arm.ArmState} {r : BitVec sz.bits}
    (hv : aluVal op (opnd sz (ρ x)) (opnd sz (ρ y)) = some r) :
    ∃ w', seqRun isem [.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)] ρ w =
        some (.fall (upd ρ d (resX sz r)) w') ∧ SameWorld F w' w := by
  obtain ⟨w', hs, hw⟩ := hR _ _ _ _ _ (ispec_aluRRR (d := d) (rn := .vreg x .int)
    (rm := .vreg y .int) (w := w) hv)
  refine ⟨w', ?_, hw⟩
  simp only [seqRun, operands_aluRRR]
  have hu : vuses #[(⟨d, .int, .def, .late, .reg⟩ : Operand), ⟨x, .int, .use, .early, .reg⟩,
      ⟨y, .int, .use, .early, .reg⟩] ρ = [ρ x, ρ y] := rfl
  rw [hu, hs]
  simp only [List.length_cons, List.length_nil, Option.map_some]
  rfl

theorem SameWorld.nf {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld F s t) :
    SameWorldNF F s t :=
  ⟨fun f hf _ => h.1 f hf, h.2.1, h.2.2⟩

theorem opnd_setWidth {sz : OperandSize} {w : Nat} (hw : w ≤ sz.bits) (hsz : sz.bits ≤ 64)
    (a : CV) : (opnd sz a).setWidth w = a.setWidth w := by
  simp only [opnd, lo64, BitVec.setWidth_setWidth_of_le _ hw,
    BitVec.setWidth_setWidth_of_le _ (Nat.le_trans hw hsz)]

theorem resX_setWidth {sz : OperandSize} {w : Nat} (hw : w ≤ sz.bits) (hsz : sz.bits ≤ 64)
    (r : BitVec sz.bits) : (resX sz r).setWidth w = r.setWidth w := by
  simp only [resX, ofX, BitVec.setWidth_setWidth_of_le _ (Nat.le_trans (Nat.le_trans hw hsz) (by omega : 64 ≤ 128)),
    BitVec.setWidth_setWidth_of_le _ (Nat.le_trans hw hsz)]

theorem opSize_bits_le (sz : OperandSize) : sz.bits ≤ 64 := by cases sz <;> decide

theorem setWidth_sub_of_le {n w : Nat} (hw : w ≤ n) (a b : BitVec n) :
    (a - b).setWidth w = a.setWidth w - b.setWidth w := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hw, BitVec.setWidth_neg_of_le hw,
    ← BitVec.sub_eq_add_neg]

/-- **Width lemma** for the five ALU operations: the operation at the operation size,
truncated to the CLIF width, is the CLIF operation of the truncations (the upper bits of the
inputs are irrelevant). -/
theorem aluVal_holds {op : ALUOp} {cop : Clif.BinaryOp}
    (hop : (op, cop) = (.add, .iadd) ∨ (op, cop) = (.sub, .isub) ∨ (op, cop) = (.and, .band) ∨
      (op, cop) = (.orr, .bor) ∨ (op, cop) = (.eor, .bxor))
    {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a b : CV}
    {u v : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) (hb : VHolds ⟨ty, v⟩ b) :
    ∃ r, aluVal op (opnd sz a) (opnd sz b) = some r ∧
      VHolds ⟨ty, Clif.Sem.binary cop u v⟩ (resX sz r) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha hb ⊢
  rcases hop with h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    refine ⟨_, rfl, ?_⟩ <;> rw [resX_setWidth hw h64]
  · rw [BitVec.setWidth_add _ _ hw, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]; rfl
  · rw [setWidth_sub_of_le hw, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]; rfl
  · rw [BitVec.setWidth_and, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]; rfl
  · rw [BitVec.setWidth_or, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]; rfl
  · rw [BitVec.setWidth_xor, opnd_setWidth hw h64, opnd_setWidth hw h64, ha, hb]; rfl

/-! ## The two-register ALU template -/

theorem ofClif_int_width {ty : Clif.Ty} : CTy.ofClif ty = .int ty.width := by cases ty <;> rfl

theorem eTy_width {ty : Clif.Ty} (h : eTy ty = true) : ty.width ≤ 64 := by
  cases ty <;> first | decide | simp [eTy] at h

set_option maxRecDepth 20000 in
theorem variantNames_Binary : (variantNames 152)[2]? = some "Binary" := rfl

/-- The instruction data and result type of a two-register instruction `cop` (from
`instData`). -/
theorem instData_binary_data {f : Clif.Function} {cop : Clif.BinaryOp} {n : String}
    (hcop : binaryOpcode cop = some n) {ty : Clif.Ty} {x y ko : Nat} {fs : List V}
    (h : instData f (.binary cop ty x y) = .ok (.data 152 2 (.data 151 ko [] :: fs))) :
    eTy ty = true ∧ fs = [.values [x, y]] := by
  simp only [instData, hcop] at h
  split at h
  · rename_i he
    refine ⟨he, ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
  · cases h

/-- **Template: a two-register ALU root rule.** A root rule whose pattern is
`(inst_data_value tyPat (Binary (O) (x y)))` for the opcode of `cop`, whose match phase and
right-hand side evaluate as `hmatch` / `hrhs` / `hnone` say (emit one `AluRRR aop` of the
operand size of the type, result in a fresh vreg), satisfies `LowerRuleOk` whenever `aop` is
`cop` on the low bits (`aluVal_holds`). A rule of this family costs its three forward
lemmas (`IselRulesALU`). -/
theorem aluRR_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {aop : ALUOp}
    {n : String} {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (hshift : cop.isShift = false)
    (hop : (aop, cop) = (.add, .iadd) ∨ (aop, cop) = (.sub, .isub) ∨ (aop, cop) = (.and, .band) ∨
      (aop, cop) = (.orr, .bor) ∨ (aop, cop) = (.eor, .bxor))
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x y st tr m,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) =
        .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)))
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x y w (rx ry : Reg) (st : LState) tr n,
      cfg.checkOverlap = false → ctx.valueReg? x = some rx → ctx.valueReg? y = some ry → w ≤ 64 →
      ∃ tr', (evalExpr p (sem ctx) cfg (n + 40) r.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
          (st, tr) =
        .ok (some (.regsVec [[(st.fresh .int).1]]),
          ((st.fresh .int).2.emit (.aluRRR aop (if w ≤ 32 then .size32 else .size64)
            (st.fresh .int).1 rx ry), tr')))
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x y w st tr n v s',
      (ctx.valueReg? x = none ∨ ctx.valueReg? y = none) →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
        (st, tr) ≠ .ok (some v, s')) :
    ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
      Refines F isem → MRStable F MR → LowerRuleOk isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr'
    hm hn _hvb _hfirst hmatch' heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  -- 1. the instruction
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2449 term_2449_kind hto hko
    (m := m' + 1) hmatch'
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Binary] at hf
  rw [hname] at ho
  have hnm : instNames inst = ("Binary", n) :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, y, rfl⟩ := instNames_binary hcop hnm
  obtain ⟨hety, hfs⟩ := instData_binary_data hcop hdat
  subst hfs
  have hw := eTy_width hety
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width]
  -- 2. determinism: the environment and the emitted code
  rw [hmatch ctx cfg ii info ty.width x y st tr m' hi hhead hw hd] at hmatch'
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch'
  obtain ⟨rfl, rfl⟩ := hmatch'
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (hnone ctx cfg x y ty.width st tr n' out (st', tr') (.inl hrx))
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (hnone ctx cfg x y ty.width st tr n' out (st', tr') (.inr hry))
  | some ry =>
  have ex := hctx.valueReg x rx hrx
  have ey := hctx.valueReg y ry hry
  subst ex ey
  obtain ⟨tr'', he⟩ := hrhs ctx cfg x y ty.width _ _ st tr n' hco hrx hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  -- 3. the meaning
  let sz : OperandSize := if ty.width ≤ 32 then .size32 else .size64
  have hsz : ty.width ≤ sz.bits := by
    by_cases h32 : ty.width ≤ 32 <;> simp [sz, h32, OperandSize.bits] <;> omega
  refine ⟨[.aluRRR aop sz (.vreg st.nextVreg .int) (.vreg x .int) (.vreg y .int)],
    [[.vreg st.nextVreg .int]], ?_, rfl, ?_⟩
  · show st.emitted.push _ = st.emitted ++ [_].toArray
    rw [Array.push_eq_append]
    rfl
  refine ⟨by simp [LState.emit, LState.fresh], ?_, ?_⟩
  · intro mi hmi d hdm
    simp only [List.mem_singleton] at hmi
    subst hmi
    have : d = st.nextVreg := by simpa [vdefs, operands_aluRRR, Operand.isDef] using hdm
    subst this
    simp [LState.emit, LState.fresh]
  intro fr cm ρ w _ hvals _ hmr
  have hout : instOutcome env cp fr cm (.binary cop ty x y) = Clif.evalInst fr cm (.binary cop ty x y) := rfl
  rw [hout]
  simp only [Clif.evalInst, hshift, Bool.false_eq_true, ↓reduceIte]
  cases hx : fr.getAs x ty with
  | trap c => simp [bind, Clif.Res.bind, explicitTrapInst]
  | stuck msg => simp [bind, Clif.Res.bind, explicitTrapInst]
  | ok u =>
  cases hy : fr.getAs y ty with
  | trap c => simp [bind, Clif.Res.bind, explicitTrapInst]
  | stuck msg => simp [bind, Clif.Res.bind, explicitTrapInst]
  | ok v =>
  simp only [bind, Clif.Res.bind, pure]
  have hxv := getAs_ok hx
  have hyv := getAs_ok hy
  obtain ⟨res, hres, hheld⟩ := aluVal_holds hop hsz (hvals x _ hxv) (hvals y _ hyv)
  obtain ⟨w', hrun, hsame⟩ := seqRun_aluRRR hR (d := st.nextVreg) (w := w) hres
  refine ⟨?_, _, w', hrun, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsame.nf hmr⟩
  · intro mi hmi u hu
    simp only [List.mem_singleton] at hmi
    subst hmi
    have : u = x ∨ u = y := by simpa [vuseNums, operands_aluRRR, Operand.isUse] using hu
    rcases this with rfl | rfl
    · exact .inr (by simp [hxv])
    · exact .inr (by simp [hyv])
  · intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), by simpa [upd] using hheld⟩
    | _ + 1, hrs, _ => simp at hrs

theorem SameWorld.trans' {F : BitVec 64 → Prop} {s t u : Arm.ArmState} (h1 : SameWorld F s t)
    (h2 : SameWorld F t u) : SameWorld F s u :=
  ⟨fun f hf => (h1.1 f hf).trans (h2.1 f hf), fun a ha => (h1.2.1 a ha).trans (h2.2.1 a ha),
    h1.2.2.trans h2.2.2⟩

theorem getAs_isSome {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {u : BitVec ty.width}
    (h : fr.getAs x ty = .ok u) : (fr.regs x).isSome := by
  simp [getAs_ok h]

end Backend.Proof
