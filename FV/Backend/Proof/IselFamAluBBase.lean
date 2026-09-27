import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.IselRulesALU

/-!
# Family B (unary ALU, shifts, rotates): shared proof infrastructure

* **World-independent straight-line code** (`PRun`): every form the family emits reads and
  writes vregs only (`ispec` returns the world unchanged), so a run of the emitted code under
  any `isem` refining `ispec` is described by the final vreg file alone, up to `SameWorld`.
  `prun_cons` composes one instruction; `prun_rr`/`prun_rrr` are its one- and two-use shapes.
* **`LowerInstOk` for one-result pure instructions** (`lowerInstOk_one`): from the monotone
  fresh-vreg facts and a `PRun` whose final file holds the CLIF result.
* **Which instruction matched** (`unary_front`, `binary_front`, …): the root rule's pattern and
  `CtxInv` fix the CLIF instruction, its type and its data.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- A two-variable rule environment as the matcher builds it. -/
abbrev env2 (a b : V) : Interp.Env V :=
  ((Array.replicate 2 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)

/-! ## World-independent straight-line runs -/

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem SameWorld.rfl' (s : Arm.ArmState) : SameWorld F s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem SameWorld.trans' {a b c : Arm.ArmState} (h1 : SameWorld F a b) (h2 : SameWorld F b c) :
    SameWorld F a c :=
  ⟨fun f hf => (h1.1 f hf).trans (h2.1 f hf), fun x hx => (h1.2.1 x hx).trans (h2.2.1 x hx),
    h1.2.2.trans h2.2.2⟩

/-- `ms` runs to completion from the vreg file `ρ`, ending in `ρ'`, from every world, with a
world that agrees with the start outside the allocatable registers. -/
def PRun (F : BitVec 64 → Prop) (isem : Sem) (ms : List MInst) (ρ ρ' : Nat → CV) : Prop :=
  ∀ w, ∃ w', seqRun isem ms ρ w = some (.fall ρ' w') ∧ SameWorld F w' w

theorem prun_nil (ρ : Nat → CV) : PRun F isem [] ρ ρ := fun w => ⟨w, rfl, SameWorld.rfl' w⟩

theorem prun_cons (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {ops : Array Operand} {outs : List CV} (hops : i.operands = .ok ops)
    (hs : ∀ w, ispec i (vuses ops ρ) w = some (outs, w, .next))
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length)
    (ht : PRun F isem ms (vdefUpd ops outs ρ) ρ') : PRun F isem (i :: ms) ρ ρ' := by
  intro w
  obtain ⟨w1, h1, s1⟩ := hR _ _ _ _ _ (hs w)
  obtain ⟨w2, h2, s2⟩ := ht w1
  refine ⟨w2, ?_, s2.trans' s1⟩
  simp only [seqRun, hops, h1, hlen, ↓reduceIte, h2, Option.map_some]
  rfl

/-- One instruction with one (late) def `d` and one use `x`. -/
theorem prun_rr (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {d x : Nat} {r : CV}
    (hops : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩])
    (hs : ∀ w, ispec i [ρ x] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

/-- One instruction with one (late) def `d` and two uses `x`, `y`. -/
theorem prun_rrr (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {d x y : Nat} {r : CV}
    (hops : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
      ⟨y, .int, .use, .early, .reg⟩])
    (hs : ∀ w, ispec i [ρ x, ρ y] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

end Run

/-! ## `LowerInstOk` for an instruction with one result computed by pure code -/

theorem usesOk_of {st : LState} {fr : Clif.Frame} {ms : List MInst} (xs : List Nat)
    (hu : ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ u ∈ xs)
    (hx : ∀ x ∈ xs, (fr.regs x).isSome) : UsesOk st fr ms := by
  intro m hm u hu'
  rcases hu m hm u hu' with h | h
  · exact .inl h
  · exact .inr (hx u h)

/-- **`LowerInstOk` from a pure run.** The emitted code `ms` defines only fresh vregs, and on
every successful CLIF evaluation (a pure instruction: memory unchanged) it reads fresh vregs or
defined values and runs (`PRun`) to a vreg file holding the single result in `d`, a fresh vreg
or a defined value's vreg. -/
theorem lowerInstOk_one {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat} {st st' : LState}
    {ms : List MInst} {d : Nat} (hMR : MRStable F MR)
    (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg)
    (htrap : explicitTrapInst inst = false)
    (hrun : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) vals cm', fr.func = ctx.func →
      ValsHeld fr ρ → DFGCons ctx fr → instOutcome env cp fr cm inst = .ok (vals, cm') →
      cm' = cm ∧ UsesOk st fr ms ∧ (st.nextVreg ≤ d ∨ (fr.regs d).isSome) ∧
        ∃ v ρ', vals = [v] ∧ PRun F isem ms ρ ρ' ∧ VHolds v (ρ' d)) :
    LowerInstOk isem MR env cp ctx inst results st [[.vreg d .int]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  split
  · rename_i vals cm' ho
    obtain ⟨rfl, hu, hd, v, ρ', rfl, hp, hh⟩ := hrun fr cm ρ vals cm' hf hv hdfg ho
    obtain ⟨w', hs, hw⟩ := hp w
    refine ⟨hu, ρ', w', hs, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hw.nf hmr⟩
    intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨d, .int, rfl, hd, hh⟩
    | _ + 1, hrs, _ => simp at hrs
  · intro h; rw [htrap] at h; cases h
  · trivial

/-! ## CLIF evaluation of the family's instructions -/

theorem getAs_isSome {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {u : BitVec ty.width}
    (h : fr.getAs x ty = .ok u) : (fr.regs x).isSome := by
  rw [getAs_ok h]; rfl

theorem evalInst_unary_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.UnaryOp}
    {ty : Clif.Ty} {x : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.unary op ty x) = .ok (vals, cm')) :
    ∃ u, fr.getAs x ty = .ok u ∧ vals = [⟨ty, Clif.Sem.unary op u⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hx : fr.getAs x ty with
  | ok u =>
    rw [hx] at h
    simp only [bind, Clif.Res.bind, pure] at h
    cases h
    exact ⟨u, rfl, rfl, rfl⟩
  | trap c => rw [hx] at h; cases h
  | stuck m => rw [hx] at h; cases h

/-! ## Which instruction a root rule matched -/

set_option maxRecDepth 20000 in
theorem variantNames_Unary : (variantNames 152)[29]? = some "Unary" := rfl

theorem unaryOpcode_inj {a b : Clif.UnaryOp} {n : String} (ha : unaryOpcode a = some n)
    (hb : unaryOpcode b = some n) : a = b := by
  cases a <;> cases b <;> simp [unaryOpcode] at ha hb <;> subst ha <;> first | rfl | simp at hb

/-- A `Unary`-format instruction whose opcode name is that of the unary operation `cop` is
`cop` (the extends and `ireduce` have other names). -/
theorem instNames_unary {c : Clif.Inst} {cop : Clif.UnaryOp} {n : String}
    (hcop : unaryOpcode cop = some n) (h : instNames c = ("Unary", n)) :
    ∃ ty x, c = .unary cop ty x := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h <;> simp at h
  case unary op ty x =>
    have : unaryOpcode op = some n := by
      cases hb : unaryOpcode op with
      | none => rw [hb] at h; simp at h; subst h; cases cop <;> simp [unaryOpcode] at hcop
      | some m => rw [hb] at h; simp at h; rw [h]
    exact ⟨ty, x, by rw [unaryOpcode_inj this hcop]⟩
  case extend op ty x =>
    exfalso; cases op <;> cases cop <;> simp [unaryOpcode] at h hcop <;> subst hcop <;> simp at h
  case ireduce ty x =>
    exfalso; cases cop <;> simp [unaryOpcode] at hcop <;> subst hcop <;> simp at h

/-- The instruction data and result type of a unary instruction `cop` (from `instData`). -/
theorem instData_unary_data {f : Clif.Function} {cop : Clif.UnaryOp} {n : String}
    (hcop : unaryOpcode cop = some n) {ty : Clif.Ty} {x ko : Nat} {fs : List V}
    (h : instData f (.unary cop ty x) = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    eTy ty = true ∧ (cop = .bswap → ty ≠ .i8) ∧ fs = [.value x] := by
  simp only [instData, hcop] at h
  split at h
  · cases h
  · rename_i he
    simp only [Bool.not_eq_true', Bool.not_eq_false] at he
    split at h
    · cases h
    · rename_i hb
      refine ⟨he, fun hc hty => hb (by simp [hc, hty]), ?_⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      injection h3 with _ h4

/-- **Front end of a unary root rule** `(inst_data_value tyPat (Unary (O) x))`: the matched
instruction is the unary operation `cop` of the opcode `O`, at a type `ty` (not `i128`, not
`bswap.i8`), with data `Unary O x` and result type `ty`. -/
theorem unary_front {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x, inst = .unary cop ty x ∧ eTy ty = true ∧ (cop = .bswap → ty ≠ .i8) ∧
      info.data = .data 152 29 [.data 151 ko [], .value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2476 term_2476_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Unary] at hf
  rw [hname] at ho
  have hnm : instNames inst = ("Unary", n) :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, rfl⟩ := instNames_unary hcop hnm
  obtain ⟨hety, hb, hfs⟩ := instData_unary_data hcop hdat
  subst hfs
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  exact ⟨ty, x, rfl, hety, hb, hd, by rw [hres]; simp [ofClif_int_width]⟩

/-! ## Width lemmas by bit-blasting

`wcases ty hety [defs]` proves a `VHolds` goal about a CLIF type `ty` (not `i128`, `hety`) and
the operand size `szOf ty.width` chosen by `operand_size`: one case per width, the operand size
made concrete (`generalize` first: it occurs inside types), then `bv_decide`. -/

/-- The operand size `operand_size` picks for an integer type of width `w`. -/
abbrev szOf (w : Nat) : OperandSize := if w ≤ 32 then .size32 else .size64

syntax "wcases " ident ident (" [" (Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| wcases $ty $hety) => `(tactic| wcases $ty $hety [])
  | `(tactic| wcases $ty $hety [$ls,*]) => `(tactic| (
      generalize hs : szOf (Clif.Ty.width $ty) = sz at *
      cases $ty:ident <;> simp [eTy] at $hety:ident <;> simp [szOf, Clif.Ty.width] at hs <;>
        subst hs <;>
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, $ls,*] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;> bv_decide -enums))

/-- `wfix [defs]`: a `VHolds` goal at a concrete type (and concrete operand sizes). -/
syntax "wfix" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| wfix) => `(tactic| wfix [])
  | `(tactic| wfix [$ls,*]) => `(tactic| (
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Nat.left_eq_add,
        Nat.add_right_cancel_iff, Nat.add_eq_left, Nat.succ_ne_self, $ls,*] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;> bv_decide -enums))

/-! ## Instruction shapes -/

theorem vdefs_rr {i : MInst} {d x : Nat}
    (h : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩]) :
    vdefs i = [d] ∧ vuseNums i = [x] := by
  simp only [vdefs, vuseNums, h]; exact ⟨rfl, rfl⟩

theorem vdefs_rrr {i : MInst} {d x y : Nat}
    (h : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
      ⟨y, .int, .use, .early, .reg⟩]) :
    vdefs i = [d] ∧ vuseNums i = [x, y] := by
  simp only [vdefs, vuseNums, h]; exact ⟨rfl, rfl⟩

/-! ## Operand facts of the emitted forms (for the templates' `hdefs`/`huses`) -/

section Facts
variable (op : ALUOp) (bop : BitOp) (sz : OperandSize) (d x y : Nat)

theorem vdd_aluRRR : vdefs (.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)) = [d] := rfl
theorem vdu_aluRRR : vuseNums (.aluRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int)) = [x, y] := rfl
theorem vdd_aluRRR_xzr : vdefs (.aluRRR op sz (.vreg d .int) .xzr (.vreg y .int)) = [d] := rfl
theorem vdu_aluRRR_xzr : vuseNums (.aluRRR op sz (.vreg d .int) .xzr (.vreg y .int)) = [y] := rfl
theorem vdd_aluRRImm12 (i : Imm12) : vdefs (.aluRRImm12 op sz (.vreg d .int) (.vreg x .int) i) = [d] := rfl
theorem vdu_aluRRImm12 (i : Imm12) : vuseNums (.aluRRImm12 op sz (.vreg d .int) (.vreg x .int) i) = [x] := rfl
theorem vdd_aluRRImmLogic (i : ImmLogic) :
    vdefs (.aluRRImmLogic op sz (.vreg d .int) (.vreg x .int) i) = [d] := rfl
theorem vdu_aluRRImmLogic (i : ImmLogic) :
    vuseNums (.aluRRImmLogic op sz (.vreg d .int) (.vreg x .int) i) = [x] := rfl
theorem vdd_aluRRImmShift (i : Nat) :
    vdefs (.aluRRImmShift op sz (.vreg d .int) (.vreg x .int) i) = [d] := rfl
theorem vdu_aluRRImmShift (i : Nat) :
    vuseNums (.aluRRImmShift op sz (.vreg d .int) (.vreg x .int) i) = [x] := rfl
theorem vdd_bitRR : vdefs (.bitRR bop sz (.vreg d .int) (.vreg x .int)) = [d] := rfl
theorem vdu_bitRR : vuseNums (.bitRR bop sz (.vreg d .int) (.vreg x .int)) = [x] := rfl
theorem vdd_extend (sg : Bool) (a b : Nat) : vdefs (.extend (.vreg d .int) (.vreg x .int) sg a b) = [d] := rfl
theorem vdu_extend (sg : Bool) (a b : Nat) :
    vuseNums (.extend (.vreg d .int) (.vreg x .int) sg a b) = [x] := rfl

end Facts

set_option hygiene false in
/-- Discharge `∀ mi ∈ code, ∀ d ∈ vdefs mi, …` (or `vuseNums`) for a concrete code list. -/
macro "code_facts0" : tactic => `(tactic| (
  intro mi hmi d hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
  repeat' (first | (rcases hmi with rfl | hmi) | subst hmi)
  all_goals (
    simp only [vdd_aluRRR, vdu_aluRRR, vdd_aluRRR_xzr, vdu_aluRRR_xzr, vdd_aluRRImm12,
      vdu_aluRRImm12, vdd_aluRRImmLogic, vdu_aluRRImmLogic, vdd_aluRRImmShift, vdu_aluRRImmShift,
      vdd_bitRR, vdu_bitRR, vdd_extend, vdu_extend, List.mem_cons, List.mem_nil_iff, or_false]
      at hd
    omega)))

/-- Discharge a template's `hdefs`/`huses` for a concrete code list. -/
macro "code_facts" : tactic => `(tactic| (intro _ _ _ _; code_facts0))

theorem arr_push1 {α : Type} (a : Array α) (i : α) : a.push i = a ++ [i].toArray := by
  apply Array.ext'; simp
theorem arr_push2 {α : Type} (a : Array α) (i j : α) : (a.push i).push j = a ++ [i, j].toArray := by
  apply Array.ext'; simp
theorem arr_push3 {α : Type} (a : Array α) (i j k : α) :
    ((a.push i).push j).push k = a ++ [i, j, k].toArray := by
  apply Array.ext'; simp
theorem arr_push4 {α : Type} (a : Array α) (i j k l : α) :
    (((a.push i).push j).push k).push l = a ++ [i, j, k, l].toArray := by
  apply Array.ext'; simp

/-- The emitted-code and fresh-counter equations of a forward lemma's final state. -/
macro "st_facts" : tactic => `(tactic| (simp only [LState.emit, LState.fresh] <;>
  first | omega | rfl | (apply Array.ext'; simp)))

/-- A one-variable rule environment. -/
abbrev env1 (a : V) : Interp.Env V := (Array.replicate 1 none).setIfInBounds 0 (some a)

/-- A rule at index `j` of a list comes before the rule at index `i > j`. -/
theorem earlier_of_idx {L : List Rule} {r r' : Rule} {i j : Nat} (hi : L[i]? = some r)
    (hj : L[j]? = some r') (hji : j < i) : ∃ pre post, L = pre ++ r :: post ∧ r' ∈ pre := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hi
  refine ⟨L.take i, L.drop (i + 1), ?_, ?_⟩
  · conv => lhs; rw [← List.take_append_drop i L]
    rw [List.drop_eq_getElem_cons hlt, hget]
  · obtain ⟨hlt', hget'⟩ := List.getElem?_eq_some_iff.mp hj
    rw [← hget']
    exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩

theorem ty_eq_of_width {ty ty' : Clif.Ty} (h : ty.width = ty'.width) (h' : ty'.width ≠ 128) :
    ty = ty' := by
  cases ty <;> cases ty' <;> simp_all [Clif.Ty.width]

/-! ## Template: a unary root rule emitting straight-line code into fresh vregs -/

/-- **Template: a unary root rule.** Rule `r` with pattern `(inst_data_value tyPat (Unary (O)
x))` for the opcode of `cop`: when it matches, the type's width satisfies `P` (`hmatch`); its
right-hand side emits `code w b x` (`b` = the first fresh vreg) allocating `k` fresh vregs and
returns the fresh vreg `res w b` (`hrhs`), or fails when `x` has no register (`hnone`). The
code defines only its fresh vregs and reads `x` and fresh vregs; `hsem` is its meaning. -/
theorem unary_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    (E : Nat → Nat → Interp.Env V) (P : Nat → Prop) (Q : Nat → Option CTy → Prop)
    (k : Nat → Option CTy → Nat) (code : Nat → Option CTy → Nat → Nat → List MInst)
    (res : Nat → Option CTy → Nat → Nat)
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x st tr m env' s1,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 29 [.data 151 ko [], .value x] →
      (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      env' = E w x ∧ s1 = (st, tr) ∧ P w)
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x w (st : LState) tr n,
      cfg.checkOverlap = false → ctx.valueReg? x = some (.vreg x .int) → w ≤ 64 → P w →
      Q w (ctx.valueType? x) →
      ∃ (tr' : Array RuleId) (st'' : LState), (evalExpr p (sem ctx) cfg (n + 40) r.rhs
          (E w x)).run (st, tr) =
        .ok (some (.regsVec [[.vreg (res w (ctx.valueType? x) st.nextVreg) .int]]), (st'', tr')) ∧
        st''.emitted = st.emitted ++ (code w (ctx.valueType? x) st.nextVreg x).toArray ∧
        st''.nextVreg = st.nextVreg + k w (ctx.valueType? x))
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x w st tr n v s',
      (ctx.valueReg? x = none ∨ ¬ Q w (ctx.valueType? x)) →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (E w x)).run (st, tr) ≠ .ok (some v, s'))
    (hres : ∀ w T b, b ≤ res w T b)
    (hdefs : ∀ w T b x, ∀ mi ∈ code w T b x, ∀ d ∈ vdefs mi, b ≤ d ∧ d < b + k w T)
    (huses : ∀ w T b x, ∀ mi ∈ code w T b x, ∀ u ∈ vuseNums mi, b ≤ u ∨ u = x)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hsem : ∀ (ty : Clif.Ty) (T : Option CTy) (b x : Nat) (ρ : Nat → CV) (u : BitVec ty.width),
      eTy ty = true → (cop = .bswap → ty ≠ .i8) → P ty.width → Q ty.width T →
      (T = none ∨ T = some (.int ty.width)) → x < b → VHolds ⟨ty, u⟩ (ρ x) →
      ∃ ρ', PRun F isem (code ty.width T b x) ρ ρ' ∧
        VHolds ⟨ty, Clif.Sem.unary cop u⟩ (ρ' (res ty.width T b))) :
    LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
    hmatch' heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, rfl, hety, hbs, hd, hhead⟩ :=
    unary_front hp hargs hto hko hname hcop hctx hi hc (m := m' + 1) hmatch'
  have hw := eTy_width hety
  obtain ⟨rfl, rfl, hP⟩ :=
    hmatch ctx cfg ii info ty.width x st tr m' env' s1 hi hhead hw hd hfirst hmatch'
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') (.inl hrx))
  | some rx =>
  have ex := hctx.valueReg x rx hrx
  subst ex
  have hxlt := hvb x _ hrx
  by_cases hQ : Q ty.width (ctx.valueType? x)
  case neg => exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') (.inr hQ))
  obtain ⟨tr'', st'', he, hem, hnx⟩ := hrhs ctx cfg x ty.width st tr n' hco hrx hw hP hQ
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨code ty.width (ctx.valueType? x) st.nextVreg x, _, hem, rfl, ?_⟩
  refine lowerInstOk_one hMR (by omega) (fun mi hmi d hd => ?_) rfl ?_
  · have := hdefs _ _ _ _ mi hmi d hd; omega
  intro fr cm ρ vals cm' _ hvals hdfg ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho
  have hxv := getAs_ok hu
  have hT : ctx.valueType? x = none ∨ ctx.valueType? x = some (.int ty.width) := by
    cases hT : ctx.valueType? x with
    | none => exact .inl rfl
    | some t =>
      have := hdfg.2 x t _ hT hxv
      exact .inr (by rw [← this, ofClif_int_width])
  obtain ⟨ρ', hrun, hheld⟩ :=
    hsem ty (ctx.valueType? x) st.nextVreg x ρ u hety hbs hP hQ hT hxlt (hvals x _ hxv)
  refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl (hres _ _ _), _, ρ', rfl, hrun, hheld⟩
  · intro mi hmi u hu
    rcases huses _ _ _ _ mi hmi u hu with h | h
    · exact .inl h
    · exact .inr (by simp [h])
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    simp [hxv]

end Backend.Proof

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Template with per-evaluation code facts

For rules whose code depends on more than the width (e.g. on `value_type` of the operand,
`put_in_reg_zext32`), the right-hand side lemma `hrhs` states, for every successful
evaluation, the code's shape (`CodeShape`) and its meaning. -/

/-- Code `ms`, emitted from `st` to `st'`, defines only fresh vregs, reads fresh vregs or `x`,
and its result `d` is fresh. -/
structure CodeShape (st st' : LState) (ms : List MInst) (d x : Nat) : Prop where
  emitted : st'.emitted = st.emitted ++ ms.toArray
  mono : st.nextVreg ≤ st'.nextVreg
  res : st.nextVreg ≤ d
  defs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, st.nextVreg ≤ e ∧ e < st'.nextVreg
  uses : ∀ mi ∈ ms, ∀ u ∈ vuseNums mi, st.nextVreg ≤ u ∨ u = x

theorem unary_ruleOk' {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    (E : Nat → Nat → Interp.Env V) (P : Nat → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x st tr m env' s1,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 29 [.data 151 ko [], .value x] →
      (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      env' = E w x ∧ s1 = (st, tr) ∧ P w)
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x w st tr n v s', ctx.valueReg? x = none →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (E w x)).run (st, tr) ≠ .ok (some v, s'))
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x w (st : LState) tr n v s',
      cfg.checkOverlap = false → ctx.valueReg? x = some (.vreg x .int) → x < st.nextVreg →
      w ≤ 64 → P w →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (E w x)).run (st, tr) = .ok (some v, s') →
      ∃ ms d, v = .regsVec [[.vreg d .int]] ∧ CodeShape st s'.1 ms d x ∧
        ∀ (ty : Clif.Ty), ty.width = w → eTy ty = true → (cop = .bswap → ty ≠ .i8) →
        (ctx.valueType? x = none ∨ ctx.valueType? x = some (.int w)) →
        ∀ (ρ : Nat → CV) (u : BitVec ty.width), VHolds ⟨ty, u⟩ (ρ x) →
        ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, Clif.Sem.unary cop u⟩ (ρ' d)) :
    LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
    hmatch' heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, rfl, hety, hbs, hd, hhead⟩ :=
    unary_front hp hargs hto hko hname hcop hctx hi hc (m := m' + 1) hmatch'
  have hw := eTy_width hety
  obtain ⟨rfl, rfl, hP⟩ :=
    hmatch ctx cfg ii info ty.width x st tr m' env' s1 hi hhead hw hd hfirst hmatch'
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') hrx)
  | some rx =>
  have ex := hctx.valueReg x rx hrx
  subst ex
  have hxlt := hvb x _ hrx
  obtain ⟨ms, d, rfl, hsh, hsem⟩ :=
    hrhs ctx cfg x ty.width st tr n' out (st', tr') hco hrx hxlt hw hP heval
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho
  have hxv := getAs_ok hu
  have hT : ctx.valueType? x = none ∨ ctx.valueType? x = some (.int ty.width) := by
    cases hT : ctx.valueType? x with
    | none => exact .inl rfl
    | some t =>
      have := hdfg.2 x t _ hT hxv
      exact .inr (by rw [← this, ofClif_int_width])
  obtain ⟨ρ', hrun, hheld⟩ := hsem ty rfl hety hbs hT ρ u (hvals x _ hxv)
  refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl hsh.res, _, ρ', rfl, hrun, hheld⟩
  · intro mi hmi u hu
    rcases hsh.uses mi hmi u hu with h | h
    · exact .inl h
    · exact .inr (by simp [h])
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    simp [hxv]

end Backend.Proof
