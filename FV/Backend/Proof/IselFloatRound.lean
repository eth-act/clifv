import FV.Backend.Proof.IselFloatArith

/-!
# S11f: scalar float rounding roots (ceil/floor/trunc/nearest) over float-capable contexts

The `lower` roots of the scalar float rounding operations (`lower.isle:567-603`), proven over
`CtxInvT` (`LowerRuleOkT`) against the shared IEEE core: CLIF's `Inst.float ceil/floor/trunc/
nearest` (`Clif.FSem.unary`: `IEEE.roundInt` with `rpi`/`rmi`/`rz`/`rne`) and the Arm instruction
the rules emit (`ispecFP`'s `fpuRound` arm, the Arm model's `FPRoundInt` with `FPCR = 0`) are the
same `IEEE.roundInt` at the same mode, so each rule is a statement about one function:

* `ceil` (`frintp`): `rule_lower_567` (f32), `rule_lower_570` (f64), `FpuRoundMode.plus32/64`;
* `floor` (`frintm`): 578/581, `minus32/64`;
* `trunc` (`frintz`): 589/592, `zero32/64`;
* `nearest` (`frintn`): 600/603, `nearest32/64`.

The generic-size rules (`lower.isle:564/575/586/597`, priority -1) are excluded: their
`fpu_round` term takes a dynamic `scalar_size ty`, which `instData`'s proven path does not cover,
so they stay unproven (like `fcmp`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Internal term: `fpu_round` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_round` (`inst.isle:2921`): `MInst.FpuRound` into a fresh float vreg. -/
theorem fpu_round_ok {n : Nat} (hn : 40 ≤ n) {op a : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 408 [op, a] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 74 [op, .reg rd, a]) := by
  isel_split hp hc h 408
  isel_inv [*, rule_inst_2921, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

end Terms

/-! ## Opcode names -/

theorem variantNames_Ceil : (variantNames 151)[124]? = some "Ceil" := rfl
theorem variantNames_Floor : (variantNames 151)[125]? = some "Floor" := rfl
theorem variantNames_Trunc : (variantNames 151)[126]? = some "Trunc" := rfl
theorem variantNames_Nearest : (variantNames 151)[127]? = some "Nearest" := rfl

/-! ## CLIF semantics of the operations -/

/-- The `FpuRoundMode` a rounding operation at a type uses (`lower.isle:567-603`): `ceil` is
round toward +∞ (`plus`), `floor` toward -∞ (`minus`), `trunc` toward zero (`zero`), `nearest`
to nearest even (`nearest`), at the type's precision. -/
def fpuRoundAt : Clif.FOp → Clif.Ty → Option FpuRoundMode
  | .ceil, .f32 => some .plus32
  | .ceil, .f64 => some .plus64
  | .floor, .f32 => some .minus32
  | .floor, .f64 => some .minus64
  | .trunc, .f32 => some .zero32
  | .trunc, .f64 => some .zero64
  | .nearest, .f32 => some .nearest32
  | .nearest, .f64 => some .nearest64
  | _, _ => none

/-- **A rounding operation is the `FpuRound` the rule emits**: on a register value holding the
operand, `fpuRoundOut` holds CLIF's result (both are `IEEE.roundInt` at the same mode). -/
theorem round_holds {op : Clif.FOp} {ty : Clif.Ty} {mo : FpuRoundMode}
    (hat : fpuRoundAt op ty = some mo) {a r : Clif.Val} {za : CV} (ha : VHolds a za)
    (h : Clif.evalFloat op ty [a] = .ok r) : ∃ z, fpuRoundOut mo za = some z ∧ VHolds r z := by
  cases op <;> cases ty <;>
    simp only [fpuRoundAt, reduceCtorEq, Option.some.injEq] at hat <;>
    obtain ⟨rfl, rfl⟩ := hat <;>
    simp only [Clif.evalFloat, Clif.FSem.unary, bind, Clif.Res.bind, beq_self_eq_true,
      ↓reduceIte] at h
  all_goals
    first
      | (cases ha' : a.at .f32 with
         | ok xa =>
           obtain rfl := val_at_ok ha'
           simp only [ha', Clif.FSem.lift1, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
           subst h
           have ha2 : za.setWidth 32 = xa := ha
           refine ⟨_, rfl, ?_⟩
           show VHolds _ ((IEEE.roundInt .b32 _ (za.setWidth 32)).setWidth 128)
           rw [ha2]; exact vholds_f32' _
         | trap _ => simp [ha'] at h
         | stuck _ => simp [ha'] at h)
      | (cases ha' : a.at .f64 with
         | ok xa =>
           obtain rfl := val_at_ok ha'
           simp only [ha', Clif.FSem.lift1, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
           subst h
           have ha2 : za.setWidth 64 = xa := ha
           refine ⟨_, rfl, ?_⟩
           show VHolds _ ((IEEE.roundInt .b64 _ (za.setWidth 64)).setWidth 128)
           rw [ha2]; exact vholds_f64' _
         | trap _ => simp [ha'] at h
         | stuck _ => simp [ha'] at h)

/-! ## `LowerInstOk` of the emitted instruction -/

/-- **`LowerInstOk` of a rounding operation lowered to `FpuRound`** into the fresh vreg
`st.nextVreg`. -/
theorem lowerInstOk_fround {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.FOp} {ty : Clif.Ty} {x : Nat}
    {mo : FpuRoundMode} (hat : fpuRoundAt op ty = some mo) {cx : RegClass}
    {results : List Nat} {st : LState} (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerInstOk isem MR env cp ctx (.float op ty [x]) results st [[.vreg st.nextVreg .float]]
      ((st.fresh .float).2.emit (.fpuRound mo (.vreg st.nextVreg .float) (.vreg x cx)))
      [.fpuRound mo (.vreg st.nextVreg .float) (.vreg x cx)] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    have hv : vdefs (.fpuRound mo (.vreg st.nextVreg .float) (.vreg x cx)) = [st.nextVreg] := rfl
    rw [hv, List.mem_singleton] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro fr cm ρ vals cm' _ hvals _ ho
    have ho' : Clif.evalInst fr cm (.float op ty [x]) = .ok (vals, cm') := ho
    obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, hx, rfl⟩ := getMany_one hv
    obtain ⟨z, hz, hrz⟩ := round_holds hat (hvals x a hx) hr
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r, upd ρ st.nextVreg z, rfl,
      prun_rr_c (r := z) hR rfl (fun w => ?_) (prun_nil _), ?_⟩
    · refine usesOk_of [x] ?_ (by simp [hx])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      have hu' : vuseNums (.fpuRound mo (.vreg st.nextVreg .float) (.vreg x cx)) = [x] := rfl
      rw [hu'] at hu
      exact .inr hu
    · first
        | (show ispecFP (.fpuRound mo (.vreg st.nextVreg .float) (.vreg x cx)) [ρ x] w = _
           simp only [ispecFP, hz, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, hz, Option.map_some]; rfl)
    · simp only [upd, ↓reduceIte]
      exact hrz

/-! ## The right-hand sides -/

/-- The variant index of an `FpuRoundMode` (`inst.isle`'s order). -/
def fpuRoundIdx : FpuRoundMode → Nat
  | .minus32 => 0 | .minus64 => 1 | .plus32 => 2 | .plus64 => 3
  | .zero32 => 4 | .zero64 => 5 | .nearest32 => 6 | .nearest64 => 7

/-- The `FpuRound` an `fpu_round` of mode index `k` emitted. -/
theorem ofV_fpuRound {o : FpuRoundMode} {k : Nat} (hk : k = fpuRoundIdx o) {rd rn : Reg}
    {m : MInst} (h : MInst.ofV (.data 58 74 [.data 103 k [], .reg rd, .reg rn]) = some m) :
    m = .fpuRound o rd rn := by
  cases o <;> simp only [fpuRoundIdx] at hk <;> subst hk <;>
    exact Option.some.inj (h.symm.trans rfl)

/-- The end of a rounding root's right-hand side: `output_reg (fpu_round mo (put_in_reg x))`
with the operand's register and the mode known. -/
theorem round_core {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {ctx : Ctx} {cfg : Config} (hco : cfg.checkOverlap = false)
    {results : List Nat} {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {mo : FpuRoundMode}
    (hat : fpuRoundAt op ty = some mo) {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2)
    {st st' : LState} {tr tr' : Array RuleId} {out w7 : V} {w6 : LState × Array RuleId}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w7] w6 out (st', tr'))
    (h408 : ApplyInternal p (sem ctx) cfg n2 27 408 [.data 103 (fpuRoundIdx mo) [],
      .reg (.vreg x (valClassOf ctx x))] (st, tr) w7 w6) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st rss st' ms := by
  obtain ⟨rfl, m1, hm1, hs2⟩ := fpu_round_ok hp hco hn2 h408
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs2 hs3 hm1
  rw [hs2] at hs3
  subst hs3
  obtain rfl := ofV_fpuRound (k := fpuRoundIdx mo) rfl hm1
  refine ⟨[.fpuRound mo (.vreg st.nextVreg .float) (.vreg x (valClassOf ctx x))],
    [[.vreg st.nextVreg .float]], ?_, rfl, lowerInstOk_fround hat hR hMR⟩
  simp [LState.emit, LState.fresh]

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of a rounding root** (`output_reg (fpu_round mo (put_in_reg x))`), from
the facts the inversion of its match and evaluation leaves. -/
theorem round_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {ii : Nat} {info w : IInfo} (hi : ctx.insts[ii]? = some info)
    {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} (_hic : info.clif = some (.float op ty [x]))
    {mo : FpuRoundMode} (hat : fpuRoundAt op ty = some mo) {ko : Nat}
    (hd : info.data = .data 152 29 [.data 151 ko [], .value x])
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2)
    {st st' : LState} {tr tr' : Array RuleId} {out w7 w5 w1 : V}
    {w6 : LState × Array RuleId} {w3 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w7] w6 out (st', tr'))
    (h408 : ApplyInternal p (sem ctx) cfg n2 27 408 [.data 103 (fpuRoundIdx mo) [], w5] (w3, tr)
      w7 w6)
    (hi' : ctx.insts[ii]? = some w) (hw : V.data 152 29 [.data 151 ko [], w1] = w.data)
    (hpx : externCtor ctx T.put_in_reg [w1] st = .ok (w5, w3)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) info.results st rss st' ms := by
  obtain ⟨hwi, hw1⟩ := fdata_eq hi hd hi' hw
  subst w
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw1
  subst hw1
  obtain ⟨rx, hrx, rfl, h3⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  subst w3
  obtain rfl := hctx.valueReg x rx hrx
  exact round_core hp hR hMR hco hat hn1 hn2 h172 h408

/-! ## The matched instruction, with its type pinned by the rule -/

/-- The instruction a rounding root matched: as `fun_front`, plus the pinning of the controlling
type the rule's `constPrim` pattern performs (`sem_prim_type`, `CTy.ofName?`). -/
theorem round_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {nm : String} {xPat : Pattern} {oT : TermId} {to : Term} {ko : Nat} {op : Clif.FOp}
    {n : String} (t : Clif.Ty) (hnm : CTy.ofName? nm = some (CTy.ofClif t))
    (hargs : r.args = [.term 18 209 [.constPrim 14 nm, .term 152 2476 [.term 151 oT [], xPat]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant ko)
    (hop : fUnaryOpcode op = some n) (hn : (variantNames 151)[ko]? = some n)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x, inst = .float op ty [x] ∧ fTyOk op ty = true ∧
      info.data = .data 152 29 [.data 151 ko [], .value x] ∧ ty = t := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2476 term_2476_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, rfl, hok, rfl⟩ := instData_fun_inv hop hn hdat
  refine ⟨ty, x, rfl, hok, hd, ?_⟩
  -- Pin `ty` from the rule's `constPrim` pattern match.
  obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
  rw [hargs] at ha
  obtain ⟨e1, hp1, -⟩ := matchArgs_cons_inv ha
  obtain ⟨fs0, hx, hm⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl hp1
  rw [sem_extract] at hx
  obtain ⟨info2, hi2, rfl⟩ := ext_inst_data_value_inv hx
  obtain ⟨e2, hp3, -⟩ := matchArgs_cons_inv hm
  rw [matchPat_constPrim_iff] at hp3
  obtain ⟨c, hc, heq, -⟩ := hp3
  rw [sem_prim_type] at hc
  obtain ⟨t0, hsome, rfl⟩ := Option.map_eq_some_iff.mp hc
  simp only [sem_eq, beq_iff_eq] at heq
  rw [hi] at hi2
  cases hi2
  injection heq with hveq
  obtain rfl := Option.some.inj (hsome.symm.trans hnm)
  have hres := float_resTy hctx (fun cc h => by subst h; simp [fUnaryOpcode] at hop) hi hic
  rw [hres] at hveq
  cases ty <;> cases t <;> simp_all [CTy.ofClif]

/-! ## The eight roots -/

set_option hygiene false in
/-- A rounding root (`ceil`/`floor`/`trunc`/`nearest`, f32/f64): `round_front` (the matched
instruction, the type pinned by the rule's `constPrim` pattern), the inversion of the match and
evaluation, `round_rhs`. Arguments: the opcode term's data fact and kind, the CLIF operation,
the opcode name fact, the `FpuRoundMode`, the type. -/
macro "round_root " ht:term:max hk:term:max op:term:max hn:term:max mo:term:max t:term:max
    : tactic =>
  `(tactic| (
    intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
    obtain ⟨ty, x, rfl, hok, hd, hty⟩ := round_front hp hctx hi hic $t rfl rfl $ht $hk
      (op := $op) rfl $hn (m := m' + 9) hmatch
    have hp' := hp
    isel_inv' hp [] at hmatch heval
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 408 _ _ _ _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := round_rhs hp' hR hMR hctx hco hi (mo := $mo) hic rfl hd
      (by omega) (by omega) h1 h2 (by assumption) (by assumption) (by assumption)
    exact ⟨ms, e1, rss, e2, e3⟩))

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`ceil` of `f32`** (`rule_lower_567`, `lower.isle:567`): `frintp s32` (`plus32`). -/
theorem ceil32_okT : LowerRuleOkT isem MR env cp p rule_lower_567 := by
  round_root hp.t2408 term_2408_kind .ceil variantNames_Ceil .plus32 .f32

set_option maxHeartbeats 8000000 in
/-- **`ceil` of `f64`** (`rule_lower_570`, `lower.isle:570`): `frintp d64` (`plus64`). -/
theorem ceil64_okT : LowerRuleOkT isem MR env cp p rule_lower_570 := by
  round_root hp.t2408 term_2408_kind .ceil variantNames_Ceil .plus64 .f64

set_option maxHeartbeats 8000000 in
/-- **`floor` of `f32`** (`rule_lower_578`, `lower.isle:578`): `frintm s32` (`minus32`). -/
theorem floor32_okT : LowerRuleOkT isem MR env cp p rule_lower_578 := by
  round_root hp.t2409 term_2409_kind .floor variantNames_Floor .minus32 .f32

set_option maxHeartbeats 8000000 in
/-- **`floor` of `f64`** (`rule_lower_581`, `lower.isle:581`): `frintm d64` (`minus64`). -/
theorem floor64_okT : LowerRuleOkT isem MR env cp p rule_lower_581 := by
  round_root hp.t2409 term_2409_kind .floor variantNames_Floor .minus64 .f64

set_option maxHeartbeats 8000000 in
/-- **`trunc` of `f32`** (`rule_lower_589`, `lower.isle:589`): `frintz s32` (`zero32`). -/
theorem trunc32_okT : LowerRuleOkT isem MR env cp p rule_lower_589 := by
  round_root hp.t2410 term_2410_kind .trunc variantNames_Trunc .zero32 .f32

set_option maxHeartbeats 8000000 in
/-- **`trunc` of `f64`** (`rule_lower_592`, `lower.isle:592`): `frintz d64` (`zero64`). -/
theorem trunc64_okT : LowerRuleOkT isem MR env cp p rule_lower_592 := by
  round_root hp.t2410 term_2410_kind .trunc variantNames_Trunc .zero64 .f64

set_option maxHeartbeats 8000000 in
/-- **`nearest` of `f32`** (`rule_lower_600`, `lower.isle:600`): `frintn s32` (`nearest32`). -/
theorem nearest32_okT : LowerRuleOkT isem MR env cp p rule_lower_600 := by
  round_root hp.t2411 term_2411_kind .nearest variantNames_Nearest .nearest32 .f32

set_option maxHeartbeats 8000000 in
/-- **`nearest` of `f64`** (`rule_lower_603`, `lower.isle:603`): `frintn d64` (`nearest64`). -/
theorem nearest64_okT : LowerRuleOkT isem MR env cp p rule_lower_603 := by
  round_root hp.t2411 term_2411_kind .nearest variantNames_Nearest .nearest64 .f64

end Roots

end Backend.Proof
