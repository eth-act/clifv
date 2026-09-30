import FV.Backend.Proof.IselCmpExt

/-!
# Conditions (`CondResult`) and their consumers (flags/select family)

A `CondResult` value is what `emit_icmp`/`is_nonzero`/`is_nonzero_cmp` return: a register
tested against zero (`Zero`/`NotZero`, at an operand size), or a flag-setting instruction that
is not emitted yet together with the Arm condition to test (`Cond`). `CondShape c P` is its
structure (the vregs it mentions satisfy `P`), `CondSem ρ c b` its truth `b` in the vreg file
`ρ` (for `Cond`: the instruction sets flags on which the condition is `b`, whatever the
world). `Or`/`And` never arise in E.

Consumers: `with_flags` (producer + consumer instruction), `lower_cond_result_bool`
(`cset`, the condition as 0/1).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Flag-setting instructions and conditions -/

/-- `m` defines no vreg and, run on the use values of `ρ`, sets the flags to `ps` from any
world. -/
def SetsFlags (m : MInst) (ρ : Nat → CV) (ps : Arm.PState) : Prop :=
  ∃ ops, m.operands = .ok ops ∧ (ops.toList.filter Operand.isDef) = [] ∧
    ∀ w, ispec m (vuses ops ρ) w = some ([], Arm.write_pstate ps w, .next)

/-- Structure of a `CondResult` of E, with every vreg it mentions satisfying `P`. -/
def CondShape (c : V) (P : Nat → Prop) : Prop :=
  (∃ k i sz, c = .data 123 0 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ P k) ∨
  (∃ k i sz, c = .data 123 1 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ P k) ∨
  (∃ (mi : V) (m : MInst) (cond : Cond), c = .data 123 2 [.data 47 1 [mi], .data 96 cond.idx []] ∧
      MInst.ofV mi = some m ∧ cond ≠ .al ∧ cond ≠ .nv ∧ vdefs m = [] ∧ ∀ u ∈ vuseNums m, P u)

/-- The truth `b` of a `CondResult` in the vreg file `ρ`. -/
def CondSem (ρ : Nat → CV) (c : V) (b : Bool) : Prop :=
  (∃ k i sz, c = .data 123 0 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ (opnd sz (ρ k) == 0) = b) ∨
  (∃ k i sz, c = .data 123 1 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ (opnd sz (ρ k) != 0) = b) ∨
  (∃ (mi : V) (m : MInst) (cond : Cond) (ps : Arm.PState), c = .data 123 2 [.data 47 1 [mi], .data 96 cond.idx []] ∧
      MInst.ofV mi = some m ∧ SetsFlags m ρ ps ∧ condOn cond.bits ps = b)

theorem CondShape.mono {c : V} {P Q : Nat → Prop} (h : CondShape c P) (hPQ : ∀ k, P k → Q k) :
    CondShape c Q := by
  rcases h with ⟨k, i, sz, h1, h2, h3⟩ | ⟨k, i, sz, h1, h2, h3⟩ | ⟨mi, m, cond, h1, h2, h3, h4, h5, h6⟩
  · exact .inl ⟨k, i, sz, h1, h2, hPQ _ h3⟩
  · exact .inr (.inl ⟨k, i, sz, h1, h2, hPQ _ h3⟩)
  · exact .inr (.inr ⟨mi, m, cond, h1, h2, h3, h4, h5, fun u hu => hPQ _ (h6 u hu)⟩)

/-! ## Running a flag producer and its consumer (`cset`, `csel`) -/

section Flags
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem vdefUpd_nil (ops : Array Operand) (ρ : Nat → CV) : vdefUpd ops [] ρ = ρ := by
  simp [vdefUpd, writeV]

theorem ispec_cmp_imm0 (sz : OperandSize) (k : Nat) (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRImm12 .subS sz .xzr (.vreg k .int) ⟨0, false⟩) [a] w =
      some ([], Arm.write_pstate (cmpFlags (opnd sz a) 0) w, .next) := by
  simp [ispec, defOut, cmpFlags, Imm12.value]

theorem setsFlags_cmp_imm0 (sz : OperandSize) (k : Nat) (ρ : Nat → CV) :
    SetsFlags (.aluRRImm12 .subS sz .xzr (.vreg k .int) ⟨0, false⟩) ρ (cmpFlags (opnd sz (ρ k)) 0) :=
  ⟨_, rfl, rfl, fun w => ispec_cmp_imm0 sz k (ρ k) w⟩

theorem ispec_cset (d : Nat) {c : Cond} (hc : c ≠ .al ∧ c ≠ .nv) (w : Arm.ArmState) :
    ispec (.cset (.vreg d .int) c) [] w =
      some ([ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64)], w, .next) := by
  simp [ispec, hc.1, hc.2, defOut]

theorem ispec_csel (d a b : Nat) (c : Cond) (x y : CV) (w : Arm.ArmState) :
    ispec (.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c) [x, y] w =
      some ([ofX (if Arm.ConditionHolds c.bits w then lo64 x else lo64 y)], w, .next) := rfl

/-- The flags a `SetsFlags` instruction produced decide every condition afterwards. -/
theorem Runs.flags (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    (hm : SetsFlags m ρ ps) (w : Arm.ArmState) :
    Runs F isem [m] ρ w (fun ρ' w' => ρ' = ρ ∧ ∀ c, Arm.ConditionHolds c w' = condOn c ps) := by
  obtain ⟨ops, hops, hdef, hs⟩ := hm
  refine Runs.one hR hops (hs w) (by simp [hdef]) (SameWorldNF.write_pstate F ps w) fun w'' hw => ?_
  refine ⟨vdefUpd_nil _ _, fun c => ?_⟩
  rw [SameWorld.conditionHolds hw, conditionHolds_write_pstate]

theorem Runs.cset (hR : Refines F isem) (d : Nat) {c : Cond} (hc : c ≠ .al ∧ c ≠ .nv)
    (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.cset (.vreg d .int) c] ρ w (fun ρ' w' =>
      ρ' = upd ρ d (ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64))) :=
  Runs.one hR rfl (ispec_cset d hc w) rfl (SameWorldNF.refl F w) fun _ _ => rfl

theorem Runs.csel (hR : Refines F isem) (d a b : Nat) (c : Cond) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    Runs F isem [.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c] ρ w (fun ρ' w' =>
      ρ' = upd ρ d (ofX (if Arm.ConditionHolds c.bits w then lo64 (ρ a) else lo64 (ρ b)))) :=
  Runs.one hR rfl (ispec_csel d a b c (ρ a) (ρ b) w) rfl (SameWorldNF.refl F w) fun _ _ => rfl

/-- A flag producer then `cset`: the condition as 0/1. -/
theorem runs_flags_cset (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {cond : Cond} {b : Bool} (hm : SetsFlags m ρ ps) (hb : condOn cond.bits ps = b)
    (hc : cond ≠ .al ∧ cond ≠ .nv) (d : Nat) (w : Arm.ArmState) :
    Runs F isem [m, .cset (.vreg d .int) cond] ρ w (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if b then 1#64 else 0#64))) := by
  refine Runs.append (ms1 := [m]) (Runs.flags hR hm w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.cset hR d hc ρ1 w1).imp fun ρ' _ _ h => ?_
  rw [h, h2, condOn_invert _ hc, hb]
  cases b <;> rfl

/-- A flag producer then `csel`. -/
theorem runs_flags_csel (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {cond : Cond} {b : Bool} (hm : SetsFlags m ρ ps) (hb : condOn cond.bits ps = b)
    (d x y : Nat) (w : Arm.ArmState) :
    Runs F isem [m, .csel (.vreg d .int) (.vreg x .int) (.vreg y .int) cond] ρ w (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if b then lo64 (ρ x) else lo64 (ρ y)))) := by
  refine Runs.append (ms1 := [m]) (Runs.flags hR hm w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.csel hR d x y cond ρ1 w1).imp fun ρ' _ _ h => ?_
  rw [h, h2, hb]

end Flags

/-! ## Which flag instruction a consumer uses for a condition -/

/-- `cmp r, #0` (`lower_cond_result_bool`'s test of a `Zero`/`NotZero` register). -/
def cmpImm0 (sz : OperandSize) (k : Nat) : MInst := .aluRRImm12 .subS sz .xzr (.vreg k .int) ⟨0, false⟩

/-- `cmp r, xzr` (`lower_select`'s test). -/
def cmpXzr (sz : OperandSize) (k : Nat) : MInst := .aluRRR .subS sz .xzr (.vreg k .int) .xzr

/-- The flag instruction `m` and condition `cond` a consumer emits for `c` (`z`: its compare
against zero). -/
def CondFlag (z : OperandSize → Nat → MInst) (c : V) (m : MInst) (cond : Cond) : Prop :=
  (∃ k i sz, c = .data 123 0 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ m = z sz k ∧ cond = .eq) ∨
  (∃ k i sz, c = .data 123 1 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ m = z sz k ∧ cond = .ne) ∨
  (∃ mi, c = .data 123 2 [.data 47 1 [mi], .data 96 cond.idx []] ∧ MInst.ofV mi = some m)

theorem cond_idx_inj {a b : Cond} (h : a.idx = b.idx) : a = b := by
  have h1 := cond_ofIdx_idx a
  rw [h, cond_ofIdx_idx] at h1
  exact (Option.some.inj h1).symm

theorem condOn_cmp_zero (sz : OperandSize) (a : BitVec sz.bits) :
    condOn Cond.ne.bits (cmpFlags a 0) = (a != 0) ∧ condOn Cond.eq.bits (cmpFlags a 0) = (a == 0) := by
  cases sz
  · exact condOn_cmp_zero_32 a
  · exact condOn_cmp_zero_64 a

theorem setsFlags_cmpXzr (sz : OperandSize) (k : Nat) (ρ : Nat → CV) :
    SetsFlags (cmpXzr sz k) ρ (cmpFlags (opnd sz (ρ k)) 0) :=
  ⟨_, rfl, rfl, fun w => rfl⟩

theorem CondFlag.sem {z : OperandSize → Nat → MInst}
    (hz : ∀ sz k ρ, SetsFlags (z sz k) ρ (cmpFlags (opnd sz (ρ k)) 0)) {c : V} {m : MInst}
    {cond : Cond} (hf : CondFlag z c m cond) {ρ : Nat → CV} {b : Bool} (hs : CondSem ρ c b) :
    ∃ ps, SetsFlags m ρ ps ∧ condOn cond.bits ps = b := by
  rcases hf with ⟨k, i, sz, rfl, hi, rfl, rfl⟩ | ⟨k, i, sz, rfl, hi, rfl, rfl⟩ | ⟨mi, rfl, hm⟩ <;>
    rcases hs with ⟨k', i', sz', e, hi', hb⟩ | ⟨k', i', sz', e, hi', hb⟩ |
      ⟨mi', m', cond', ps, e, hm', hsf, hb⟩ <;> simp at e
  · obtain ⟨rfl, rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact ⟨_, hz sz k ρ, by rw [(condOn_cmp_zero sz _).2, hb]⟩
  · obtain ⟨rfl, rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact ⟨_, hz sz k ρ, by rw [(condOn_cmp_zero sz _).1, hb]⟩
  · obtain ⟨rfl, e2⟩ := e
    rw [hm] at hm'; cases hm'
    rw [cond_idx_inj e2]
    exact ⟨ps, hsf, hb⟩

theorem CondFlag.shape {z : OperandSize → Nat → MInst}
    (hz : ∀ sz k, vdefs (z sz k) = [] ∧ vuseNums (z sz k) = [k]) {c : V} {m : MInst}
    {cond : Cond} (hf : CondFlag z c m cond) {P : Nat → Prop} (hs : CondShape c P) :
    cond ≠ .al ∧ cond ≠ .nv ∧ vdefs m = [] ∧ ∀ u ∈ vuseNums m, P u := by
  rcases hf with ⟨k, i, sz, rfl, hi, rfl, rfl⟩ | ⟨k, i, sz, rfl, hi, rfl, rfl⟩ | ⟨mi, rfl, hm⟩ <;>
    rcases hs with ⟨k', i', sz', e, hi', hb⟩ | ⟨k', i', sz', e, hi', hb⟩ |
      ⟨mi', m', cond', e, hm', h1, h2, h3, h4⟩ <;> simp at e
  · obtain ⟨rfl, rfl⟩ := e
    refine ⟨by decide, by decide, (hz sz k).1, ?_⟩
    rw [(hz sz k).2]; simpa using hb
  · obtain ⟨rfl, rfl⟩ := e
    refine ⟨by decide, by decide, (hz sz k).1, ?_⟩
    rw [(hz sz k).2]; simpa using hb
  · obtain ⟨rfl, e2⟩ := e
    rw [hm] at hm'; cases hm'
    rw [cond_idx_inj e2]
    exact ⟨h1, h2, h3, h4⟩

theorem vdefs_cset (d : Nat) (c : Cond) : vdefs (.cset (.vreg d .int) c) = [d] := rfl
theorem vuseNums_cset (d : Nat) (c : Cond) : vuseNums (.cset (.vreg d .int) c) = [] := rfl

theorem Frag.fresh_emit2 (s : LState) {m1 m2 : MInst} (hd1 : vdefs m1 = [])
    (hd2 : vdefs m2 ⊆ [s.nextVreg]) :
    Frag s (((s.fresh .int).2.emit m1).emit m2) [m1, m2] := by
  refine ⟨?_, ?_, ?_⟩
  · apply Array.ext'; simp [LState.emit, LState.fresh]
  · simp [LState.emit, LState.fresh]
  · intro m' hm' d hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with rfl | rfl
    · simp [hd1] at hd'
    · have := hd2 hd'
      simp only [List.mem_singleton] at this
      simp [LState.emit, LState.fresh, this]

/-- **The code of a consumer**: a flag producer `m` then `cset`/`csel` into the fresh vreg. -/
theorem condFlag_cset_code {z : OperandSize → Nat → MInst}
    (hz : ∀ sz k, vdefs (z sz k) = [] ∧ vuseNums (z sz k) = [k]) {c : V} {m : MInst}
    {cond : Cond} (hf : CondFlag z c m cond) {P : Nat → Prop} (hs : CondShape c P) (s : LState) :
    Frag s (((s.fresh .int).2.emit m).emit (.cset (.vreg s.nextVreg .int) cond))
      [m, .cset (.vreg s.nextVreg .int) cond] ∧
    ∀ i ∈ [m, .cset (.vreg s.nextVreg .int) cond], ∀ u ∈ vuseNums i, P u := by
  obtain ⟨-, -, hd, hu⟩ := hf.shape hz hs
  refine ⟨Frag.fresh_emit2 s hd (by rw [vdefs_cset]; exact List.Subset.refl _), fun i hi u hu' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hu u hu'
  · simp [vuseNums_cset] at hu'

/-! ## Decoding emitted instruction values -/

section OfV
set_option maxRecDepth 20000

theorem ofV_cset' (rd : Reg) (c : V) :
    MInst.ofV (.data 58 33 [.reg rd, c]) = c.cond?.map (.cset rd) := by
  have e1 : MInst.ofV (.data 58 33 [.reg rd, c]) = (do return .cset rd (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

theorem ofV_cmpImm (i : Nat) (rd rn : Reg) (imm : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 i [], .reg rd, .reg rn, .op (.imm12 imm)]) =
      (OperandSize.ofIdx? i).map fun sz => .aluRRImm12 .subS sz rd rn imm := by
  have e : (V.data 93 i []).size? = OperandSize.ofIdx? i := rfl
  have e1 : MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 i [], .reg rd, .reg rn, .op (.imm12 imm)]) =
      (do return .aluRRImm12 .subS (← (V.data 93 i []).size?) rd rn imm) := rfl
  rw [e1, e]; cases OperandSize.ofIdx? i <;> rfl

theorem cond_ofIdx_0 : Cond.ofIdx? 0 = some .eq := rfl
theorem cond_ofIdx_1 : Cond.ofIdx? 1 = some .ne := rfl

end OfV

theorem cmpImm0_sets (sz : OperandSize) (k : Nat) (ρ : Nat → CV) :
    SetsFlags (cmpImm0 sz k) ρ (cmpFlags (opnd sz (ρ k)) 0) := setsFlags_cmp_imm0 sz k ρ
theorem cmpImm0_regs (sz : OperandSize) (k : Nat) :
    vdefs (cmpImm0 sz k) = [] ∧ vuseNums (cmpImm0 sz k) = [k] := ⟨rfl, rfl⟩
theorem cmpXzr_regs (sz : OperandSize) (k : Nat) :
    vdefs (cmpXzr sz k) = [] ∧ vuseNums (cmpXzr sz k) = [k] := ⟨rfl, rfl⟩

/-- **Meaning of `lower_cond_result_bool`'s code**: the fresh vreg holds the condition as 0/1. -/
theorem lcrb_run {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {c : V} {m : MInst}
    {cond : Cond} (hf : CondFlag cmpImm0 c m cond) {P : Nat → Prop} (hsh : CondShape c P)
    {ρ : Nat → CV} {b : Bool} (hs : CondSem ρ c b) (d : Nat) (w : Arm.ArmState) :
    Runs F isem [m, .cset (.vreg d .int) cond] ρ w (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if b then 1#64 else 0#64))) := by
  obtain ⟨ps, hsf, hb⟩ := hf.sem cmpImm0_sets hs
  obtain ⟨h1, h2, -, -⟩ := hf.shape cmpImm0_regs hsh
  exact runs_flags_cset hR hsf hb ⟨h1, h2⟩ d w

/-! ## Instructions a pattern can see through `def_inst` -/

/-- Every opcode name `instData` can produce (`instNames`). -/
def eOpNames : List String :=
  ["", "Iconst", "Ineg", "Bnot", "Clz", "Ctz", "Popcnt", "Bswap", "Bitrev", "Iadd", "Isub", "Imul",
   "Umulhi", "Smulhi", "Band", "Bor", "Bxor", "Ishl", "Ushr", "Sshr", "Rotl", "Rotr", "Smin", "Smax",
   "Umin", "Umax", "Udiv", "Sdiv", "Urem", "Srem", "Icmp", "Uextend", "Sextend", "Ireduce", "Load",
   "Uload8", "Sload8", "Uload16", "Sload16", "Uload32", "Sload32", "Store", "Istore8", "Istore16",
   "Istore32", "Select", "Nop", "SymbolValue", "StackAddr", "Call", "CallIndirect", "FuncAddr",
   -- agent/fv-fallback: `bmask` and the atomic opcodes (unverified, outside `E2E.InSubset`)
   "Bmask", "AtomicLoad", "AtomicStore", "AtomicRmw", "AtomicCas", "Fence"]

theorem instNames_snd_mem (cl : Clif.Inst) : (instNames cl).2 ∈ eOpNames := by
  cases cl <;> simp only [instNames] <;> try decide
  all_goals first
    | (rename_i op _ _; cases op <;> decide)
    | (rename_i op _ _ _; cases op <;> decide)
    | (rename_i op _ _ _ _; cases op <;> decide)
    | (rename_i op _ _ _ _ _; cases op <;> decide)
    | (rename_i op _ _ _ _ _ _; cases op <;> decide)

/-- An instruction reached through `def_inst` has an opcode of E: a pattern naming another
opcode never matches. -/
theorem opcode_absurd {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {x j : Nat}
    {info : IInfo} (hd : ctx.defInst? x = some j) (hi : ctx.insts[j]? = some info) {kf ko : Nat}
    {fs : List V} (he : V.data 152 kf (V.data 151 ko [] :: fs) = info.data) {s : String}
    (hs : (variantNames 151)[ko]? = some s) (hns : s ∉ eOpNames) : False := by
  have hcl := hctx.defClif x j info hd hi
  obtain ⟨cl, hcl'⟩ := Option.isSome_iff_exists.mp hcl
  have hdata := hctx.data j info cl hi hcl'
  rw [← he] at hdata
  have := (instData_inv_names hdata).2
  rw [hs] at this
  cases this
  exact hns (instNames_snd_mem cl)

open Lean Elab Tactic Meta in
/-- Close a goal whose hypotheses say an instruction reached through `def_inst` has a non-E
opcode (`opcode_absurd` over every fitting triple of hypotheses). -/
elab "isel_opcode_absurd " hctx:ident : tactic => withMainContext do
  let lctx ← getLCtx
  let hs := lctx.decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for he in hs do
    let t ← instantiateMVars he.type
    unless t.isAppOfArity ``Eq 3 do continue
    unless (t.getArg! 1).isAppOf ``Backend.V.data do continue
    for hi in hs do
      for hd in hs do
        let s ← saveState
        try
          let a ← Term.exprToSyntax (mkFVar hd.fvarId)
          let b ← Term.exprToSyntax (mkFVar hi.fvarId)
          let c ← Term.exprToSyntax (mkFVar he.fvarId)
          evalTactic (← `(tactic| exact (opcode_absurd $hctx $a $b $c rfl (by decide)).elim))
          return
        catch _ => s.restore
  throwError "isel_opcode_absurd: no fitting hypotheses"

/-! ## `with_flags`, `lower_cond_result_bool` -/

section Cons
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `with_flags` on a side-effect producer and a register-returning consumer (rule
`with_flags_consumer_reg`; the other 15 rules need other variants): emit both, return the
consumer's register. -/
theorem with_flags_ok {n : Nat} (hn : 40 ≤ n) {mi ci : V} {r : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 254 [.data 47 1 [mi], .data 49 3 [ci, .reg r]] s v s') :
    ∃ m1 m2, MInst.ofV mi = some m1 ∧ MInst.ofV ci = some m2 ∧ v = .regs [r] ∧
      s'.1 = (s.1.emit m1).emit m2 := by
  isel_split' hp hc h 254
  all_goals try (isel_refute hp at hm; done)
  case' inr.inr.inr.inr.inl =>
    isel_inv' hp [] at hm he
    exact ⟨_, ‹_›, _, ‹_›, rfl⟩
  all_goals done

theorem ctor_u8_into_imm12_0 (ctx : Ctx) (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.u8_into_imm12 [.int 0] st = .ok (v, st') ↔
      v = .op (.imm12 ⟨0, false⟩) ∧ st' = st := by
  have : externCtor ctx T.u8_into_imm12 [.int 0] st = .ok (.op (.imm12 ⟨0, false⟩), st) := rfl
  rw [this]; simp [eq_comm]

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`lower_cond_result_bool`** on a condition of E: emit the flag instruction and `cset` into a
fresh vreg. -/
theorem lcrb_ok {n : Nat} (hn : 80 ≤ n) {c : V} {P : Nat → Prop} (hsh : CondShape c P)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 715 [c] s v s') :
    ∃ m cond, CondFlag cmpImm0 c m cond ∧ v = .reg (.vreg s.1.nextVreg .int) ∧
      s'.1 = ((s.1.fresh .int).2.emit m).emit (.cset (.vreg s.1.nextVreg .int) cond) := by
  rcases hsh with ⟨k, i, sz, rfl, hi, -⟩ | ⟨k, i, sz, rfl, hi, -⟩ | ⟨mi, m, cond, rfl, hm0, -⟩ <;>
  isel_split' hp hc h 715 <;>
  (try (isel_refute hp at hm; done)) <;>
  isel_inv' hp [ctor_u8_into_imm12_0] at hm he <;>
  isel_call hp hc [cmp_imm_ok, cset_ok, with_flags_ok]
  all_goals simp only [ofV_cset', ofV_cmpImm, V.cond?_data, cond_ofIdx_0, cond_ofIdx_1, cond_ofIdx_idx,
    Option.map_some, Option.some.injEq, Option.map_eq_some_iff, ctor_value_regs_get_iff,
    Int.toNat_zero, List.getElem?_cons_zero] at *
  all_goals isel_destruct
  all_goals subst_vars
  · rename_i h1 h2 _ _ h3 _
    rw [hi] at h3; cases h3
    refine ⟨_, _, .inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩, ?_, ?_⟩ <;> (try simp only [*]) <;> rfl
  · rename_i h1 h2 _ _ h3 _
    rw [hi] at h3; cases h3
    refine ⟨_, _, .inr (.inl ⟨k, i, sz, rfl, hi, rfl, rfl⟩), ?_, ?_⟩ <;> (try simp only [*]) <;> rfl
  · rename_i h1 _
    rw [hm0] at h1; cases h1
    refine ⟨_, _, .inr (.inr ⟨mi, rfl, hm0⟩), ?_, ?_⟩ <;> (try simp only [*]) <;> rfl

end Cons

end Backend.Proof
