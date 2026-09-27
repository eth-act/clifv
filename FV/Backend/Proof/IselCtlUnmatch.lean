import FV.Backend.Proof.IselCtlBase

/-!
# Family Ctl: rules that cannot match a terminator

Every root rule of `lower`/`lower_branch` has, at the root of its first argument pattern, the
`inst_data_value` extractor with an `InstructionData` format variant (`rootFmt`, five pattern
shapes: plain, `bind`, `and` of one or two, nested `and`). The format terms are
`InstructionData.*`, term ids `2447 … 2482`, variant `fT - 2447` (`fmt_kinds`). A successful
match fixes the format of the matched instruction's data (`rootFmt_match`), so a rule whose
format differs from the terminator's (`termData`) cannot match it. The per-rule formats are
checked by one kernel decision over the exported rule list (`lower_fmts`,
`lower_branch_fmts`).

Results: `termUnmatchable` (`TermUnmatchable program`) and `branchExcludedUnmatchable`
(`BranchExcludedUnmatchable program`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-! ## The root format of a rule -/

/-- The format term of `(inst_data_value _ (InstructionData.K …))`. -/
def fmtD : Pattern → Option Nat
  | .term 18 209 [_, .term 152 fT _] => some fT
  | _ => none

/-- The format term at the root of a rule's instruction pattern. -/
def rootFmt : Pattern → Option Nat
  | .bind _ _ q => fmtD q
  | .and _ [q] => fmtD q
  | .and _ [_, .and _ [_, q]] => fmtD q
  | .and _ [_, q] => fmtD q
  | q => fmtD q

def ruleFmt (r : Rule) : Option Nat :=
  match r.args with
  | q :: _ => rootFmt q
  | [] => none

/-- The `InstructionData` format terms `2447 + i` are the enum variants `i` (`i < 36`). -/
def FmtKinds (p : Program) : Prop :=
  ∀ i, i < 36 → ∃ tf, termOf p (2447 + i) = .ok tf ∧ tf.kind = .enumVariant i

theorem fmtKinds_program : FmtKinds program := by
  have h : (List.range 36).all (fun i => match termOf program (2447 + i) with
      | .ok tf => tf.kind == .enumVariant i
      | .error _ => false) = true := by decide +kernel
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  revert this
  cases termOf program (2447 + i) with
  | error e => simp
  | ok tf => intro h; exact ⟨tf, rfl, by simpa using h⟩

section
variable {p : Program} (hp : Data p) {ctx : Ctx}

theorem matchAll_cons_inv {st : LState} {q : Pattern} {qs : List Pattern} {v : V}
    {env env' : Interp.Env V}
    (h : matchAll p (sem ctx) st (q :: qs) v env = .ok (some env')) :
    ∃ e1, matchPat p (sem ctx) st q v env = .ok (some e1) ∧
      matchAll p (sem ctx) st qs v e1 = .ok (some env') := by
  rw [matchAll.eq_2] at h
  cases hq : matchPat p (sem ctx) st q v env with
  | error e => rw [hq] at h; cases h
  | ok o =>
    rw [hq] at h
    cases o with
    | none => cases h
    | some e1 => exact ⟨e1, rfl, h⟩

theorem matchPat_and_inv {st : LState} {ty : TypeId} {qs : List Pattern} {v : V}
    {env env' : Interp.Env V}
    (h : matchPat p (sem ctx) st (.and ty qs) v env = .ok (some env')) :
    matchAll p (sem ctx) st qs v env = .ok (some env') := by
  rw [matchPat.eq_7] at h; exact h

include hp in
theorem fmtD_match_k {q : Pattern} {fT : Nat} (hq : fmtD q = some fT) {tf : Term} {k : Nat}
    (htf : termOf p fT = .ok tf) (hkf : tf.kind = .enumVariant k) {st : LState} {ti : Nat}
    {env env' : Interp.Env V} (h : matchPat p (sem ctx) st q (.inst ti) env = .ok (some env')) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 k fs := by
  unfold fmtD at hq
  split at hq
  · cases hq
    obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl h
    rw [sem_extract] at hx
    obtain ⟨info, hi, rfl⟩ := ext_inst_data_value_inv hx
    obtain ⟨e1, -, hm2⟩ := matchArgs_cons_inv hm
    obtain ⟨e2, hp2, -⟩ := matchArgs_cons_inv hm2
    obtain ⟨fs', hu, -⟩ := matchPat_enum_inv htf hkf hp2
    exact ⟨info, fs', hi, sem_unData_inv hu⟩
  · cases hq

include hp in
theorem rootFmt_match_k {q : Pattern} {fT : Nat} (hq : rootFmt q = some fT) {tf : Term} {k : Nat}
    (htf : termOf p fT = .ok tf) (hkf : tf.kind = .enumVariant k) {st : LState} {ti : Nat}
    {env env' : Interp.Env V} (h : matchPat p (sem ctx) st q (.inst ti) env = .ok (some env')) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 k fs := by
  unfold rootFmt at hq
  split at hq
  · exact fmtD_match_k hp hq htf hkf (matchPat_bind_inv h).2
  · obtain ⟨e1, h1, -⟩ := matchAll_cons_inv (matchPat_and_inv h)
    exact fmtD_match_k hp hq htf hkf h1
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    obtain ⟨e3, -, h4⟩ := matchAll_cons_inv (matchPat_and_inv h3)
    obtain ⟨e4, h5, -⟩ := matchAll_cons_inv h4
    exact fmtD_match_k hp hq htf hkf h5
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    exact fmtD_match_k hp hq htf hkf h3
  · exact fmtD_match_k hp hq htf hkf h

include hp in
/-- **A root rule that matched instruction `ti` fixes the format of its data** (the format term
`fT` of the rule is the enum variant `k`). -/
theorem ruleFmt_match_k {r : Rule} {fT : Nat} (hq : ruleFmt r = some fT) {tf : Term} {k : Nat}
    (htf : termOf p fT = .ok tf) (hkf : tf.kind = .enumVariant k) {cfg : Config} {m : Nat}
    {ti : Nat} {vs : List V} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg m r (.inst ti :: vs)).run s = .ok (some env, s1)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 k fs := by
  cases m with
  | zero => rw [matchRule.eq_1] at h; cases h
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
    unfold ruleFmt at hq
    split at hq
    · rename_i q qs hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact rootFmt_match_k hp hq htf hkf h1
    · cases hq

include hp in
theorem ruleFmt_match (hk : FmtKinds p) {r : Rule} {fT : Nat} (hq : ruleFmt r = some fT)
    (hlo : 2447 ≤ fT) (hhi : fT < 2447 + 36) {cfg : Config} {m : Nat} {ti : Nat}
    {vs : List V} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg m r (.inst ti :: vs)).run s = .ok (some env, s1)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT - 2447) fs := by
  have hlt : fT - 2447 < 36 := by omega
  obtain ⟨tf, htf, hkf⟩ := hk (fT - 2447) hlt
  rw [show 2447 + (fT - 2447) = fT by omega] at htf
  exact ruleFmt_match_k hp hq htf hkf h

/-- The `InstructionData` variant of each terminator's data (`termData`). -/
def termFmt : Clif.Terminator → Nat
  | .jump _ => 15 | .brif .. => 5 | .brTable .. => 4 | .ret _ => 18 | .trap _ => 26
  | .returnCall .. => 0

/-- A terminator whose data has format `termFmt t`. -/
theorem termData_fmt {t : Clif.Terminator} {data : V} (hd : termData t = .ok data) :
    ∃ fs, data = .data 152 (termFmt t) fs := by
  cases t with
  | jump d => rw [termData_jump] at hd; cases hd; exact ⟨_, rfl⟩
  | brif c a b => rw [termData_brif] at hd; cases hd; exact ⟨_, rfl⟩
  | brTable x d tb => rw [termData_brTable] at hd; cases hd; exact ⟨_, rfl⟩
  | ret xs => rw [termData_ret] at hd; cases hd; exact ⟨_, rfl⟩
  | trap c => rw [termData_trap] at hd; cases hd; exact ⟨_, rfl⟩
  | returnCall fn args => simp [termData, throw, throwThe, MonadExceptOf.throw] at hd

include hp in
/-- **The terminator a rule matched**: a rule whose root format is the enum variant `k` matched
the terminator placeholder `ti` of `t` only if `t`'s format is `k`. -/
theorem ruleFmt_term {r : Rule} {fT : Nat} (hq : ruleFmt r = some fT) {tf : Term} {k : Nat}
    (htf : termOf p fT = .ok tf) (hkf : tf.kind = .enumVariant k) {t : Clif.Terminator}
    {data : V} (hd : termData t = .ok data) {ti : Nat} (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {cfg : Config} {m : Nat} {vs : List V} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg m r (.inst ti :: vs)).run s = .ok (some env, s1)) :
    termFmt t = k := by
  obtain ⟨info, fs, hinfo, hdat⟩ := ruleFmt_match_k hp hq htf hkf h
  rw [hi] at hinfo
  cases hinfo
  obtain ⟨fs', rfl⟩ := termData_fmt hd
  simp only [V.data.injEq] at hdat
  exact hdat.2.1

end

/-! ## The formats of the exported rules -/

/-- Every rule of `lower` other than the terminator rules names a format other than
`MultiAry` (2465, `return`) and `Trap` (2473, `trap`). -/
def lowerFmtOk (r : Rule) : Bool :=
  termRootRule r ||
    match ruleFmt r with
    | some fT => 2447 ≤ fT && fT < 2447 + 36 && fT != 2465 && fT != 2473
    | none => false

theorem lower_fmts : (program.rulesOf TId.lower).all lowerFmtOk = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- Every rule of `lower_branch` outside the closure names a format other than `Jump` (2462),
`Brif` (2452) and `BranchTable` (2451). -/
def branchFmtOk (r : Rule) : Bool :=
  closureRoot r ||
    match ruleFmt r with
    | some fT => 2447 ≤ fT && fT < 2447 + 36 && fT != 2462 && fT != 2452 && fT != 2451
    | none => false

theorem lower_branch_fmts : (program.rulesOf TId.lower_branch).all branchFmtOk = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

/-! ## The two statements -/

/-- **`TermUnmatchable`**: no rule of `lower` other than 964/1037 matches a `return`/`trap`. -/
theorem termUnmatchable : TermUnmatchable program := by
  intro r hr hroot f ctx hctx ti t data hrt hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_fmts r hr
  simp only [lowerFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

/-- **`BranchExcludedUnmatchable`**: the `try_call` rules of `lower_branch` never match a
branch. -/
theorem branchExcludedUnmatchable : BranchExcludedUnmatchable program := by
  intro r hr hroot f ctx hctx ti t data targets hrt hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_fmts r hr
  simp only [branchFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩, h3⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

end Backend.Proof
