import FV.E2E.RegLevelU
import FV.E2E.RegLevelCallSite

/-!
# A raising `try_call` on the machine: the landing pad (S10e, #232)

`realizes_tryCall_raiseU`: from `Q` at a `tryCall` item whose callee raises (`XRaise`), one step
of the machine with unwinding (`Unw.ArmStepU`: the callee raises, the personality reads the
emitted call-site table and installs the first handler's landing pad) reaches `Q` at the entry
of the handler's successor (the landing-pad edge block, whose label line is at the pad's
offset: `pad_label`), the defs of the call holding the payload (x0 = the exception object,
x1 = 0; every other allocatable register as the unwinder restored it, x0/x1 holding nothing
live by `tryUOk`'s `payloadRegOk`): the raising `tryCall` case of `realizes_allU`, for any
semantics with `csemU`'s raising-`tryCall` clause (`TryRaiseSem`), the trace state the
raising-call state (`RLU.RaiseX`).

What it reads about the emitted code and tables:
* `LsdaAt`: the tables the unwinder reads hold the emitted call-site table (`CallSitesOk`);
* `PadsNonzero`: the landing pads of the table are at non-zero offsets (the personality treats
  landing pad 0 as none); decidable check `padsNonzeroB` (`padsNonzero_of_check`);
* `SiteAt`: the call-site bridge: at a call item the pc is at the call line whose return
  offset `callSites` pairs with this call; `siteAt_of_check` from `q_callSite`/
  `q_callSite_last` under the check `lastCallsOk`.
* Non-vacuity: `UTryWitness.checks` (both checks pass on S10c's witness function).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables

/-- The tables the unwinder reads hold the emitted call-site table of the activation's
function. -/
def LsdaAt (R : RLU) : Prop :=
  ∃ sites, CallSitesOk R.af R.fa sites ∧ R.T.lsda = some (sites.map (·.entry))

/-- The labels `callSites` resolves landing pads with: the block-label aliases of the final code
(`fa.alias`, at the offset of the label each resolves to), then the labels of the final code. -/
def siteLabs (fa : FnAsm) : List (Label × Nat) :=
  fa.alias.filterMap (fun l =>
    ((scanLines fa.lines.toList 0 [] []).1.lookup l.2).map fun x => (l.1, x)) ++
  (scanLines fa.lines.toList 0 [] []).1

/-- Every `try_call` landing pad of the emitted call-site table is at a non-zero offset. (Since
#553 the entries are looked up in the alias-extended labels `siteLabs`, as `callSites` does.) -/
def PadsNonzero (af : AFunc) (fa : FnAsm) : Prop :=
  ∀ ti ret e, (some ti, ret) ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2 →
    entryFor (siteLabs fa) (some ti, ret) = some e → e.pad ≠ 0

/-- **The call-site bridge** at the call items of the activation: the pc is at the call line,
whose return offset `callSites` pairs with this call (`none` for a `call`, `some ti` for a
`tryCall`). -/
def SiteAt (R : RL) : Prop :=
  ∀ (s : Arm.ArmState) (b k : Nat) (allocs : Array Loc) (its : List RItem) (m : Loc → CV)
    (w : Arm.ArmState) (vb : VBlock) (i : MInst) (info : CallInfo) (c : Option TryInfo),
    Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) → R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → ((i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti) →
    ∃ j x, R.L[j]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      (c, lineOffset R.L j + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2

/-! ## List facts -/

theorem mem_zip_filter_map {α β γ : Type} (P : α → Bool) (g : α → γ) :
    ∀ (L : List (α × β)) (q : (α × β) × γ),
      q ∈ (L.filter (fun p => P p.1)).zip (((L.map Prod.fst).filter P).map g) → q.2 = g q.1.1
  | [], _, h => by simp at h
  | a :: L, q, h => by
    by_cases ha : P a.1 = true
    · simp only [List.filter_cons, ha, ite_true, List.map_cons, List.zip_cons_cons,
        List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact mem_zip_filter_map P g L q h
    · simp only [List.filter_cons, ha, List.map_cons, Bool.false_eq_true, ite_false] at h
      exact mem_zip_filter_map P g L q h

theorem zip_toList_map_fst {α β : Type} (xs : Array α) (ys : Array β) (h : xs.size = ys.size) :
    (xs.zip ys).toList.map Prod.fst = xs.toList := by
  rw [Array.toList_zip, List.map_fst_zip]
  simp [h]

/-! ## Registers after the landing pad's install -/

theorem regVal_x01 {t : Arm.ArmState} {obj : BitVec 64} {r : Reg}
    (ha : r.allocatable = true) (h0 : r ≠ .x 0) (h1 : r ≠ .x 1) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) r = regVal t r := by
  rcases allocatable_cases ha with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, hn⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [e])
    have hn1 : n ≠ 1 := fun e => h1 (by rw [e])
    simp only [regVal, rnum]
    rw [Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 1) (by omega) (by omega) hn1),
      Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]
        exact Unw.ofNat5_ne (a := n) (b := 0) (by omega) (by omega) hn0)]
  · simp only [regVal]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]

theorem regVal_x01_x0 (t : Arm.ArmState) (obj : BitVec 64) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) (.x 0) = ofX obj := by
  simp only [regVal, rnum, ofX]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem regVal_x01_x1 (t : Arm.ArmState) (obj : BitVec 64) :
    regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) (.x 1) = ofX 0 := by
  simp only [regVal, rnum, ofX]
  rw [Arm.r_of_w_same]

theorem frameKeep_x01 {F : BitVec 64 → Prop} {s t : Arm.ArmState} {obj : BitVec 64}
    (h : FrameKeep F s t) :
    FrameKeep F s (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) := by
  refine ⟨?_, fun a ha => ?_⟩
  · simp only [spOf]
    rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide)]
    exact h.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]
    exact h.2 a ha

theorem sameWorld_x01 {F : BitVec 64 → Prop} {t w : Arm.ArmState} {obj : BitVec 64}
    (h : SameWorld F t w) :
    SameWorld F (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) w :=
  SameWorld.w_left (by simp [Masked]) (SameWorld.w_left (by simp [Masked]) h)

theorem err_x01 {t : Arm.ArmState} {obj : BitVec 64} (h : Arm.r .ERR t = .None) :
    Arm.r .ERR (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) = .None := by
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
  exact h

/-- A fixed def operand's allocated register is its fixed register. -/
theorem def_fixed_reg {cc : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clob : List Reg} (hst : cc.checkStatic wh ops (regs.map Loc.reg) clob = .ok ())
    {o : Operand} (ho : o ∈ ops.toList) (hd : o.isDef = true) {r : Reg} (hc : o.con = .fixed r) :
    ∃ p ∈ (ops.zip regs).toList, p.1.isDef = true ∧ p.2 = r := by
  obtain ⟨hsz, hfx, -, -⟩ := checkStatic_facts hst
  simp only [Array.size_map] at hsz
  rw [← zip_toList_map_fst ops regs hsz] at ho
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  refine ⟨p, hp, hd, ?_⟩
  have hp' : (p.1, Loc.reg p.2) ∈ (ops.zip (regs.map Loc.reg)).toList := by
    rw [pairs_regs]; exact List.mem_map_of_mem hp
  have := (hfx _ hp').2 r hc
  simpa using this

/-! ## The landing pad -/

/-- The landing pad the call-site table gives a `try_call` whose first handler is `tag 0`/`tag 1`
of label `l` is the offset of `l`'s label line. -/
theorem pad_label {R : RL} (hR : R.Wf) {ti : TryInfo} {ret : Nat} {e : Unw.CallSiteEntry}
    {h : TryHandler} {hs : List TryHandler} (hti : ti.handlers = h :: hs) {l : Label}
    (hl : h = .tag 0 l ∨ h = .tag 1 l)
    (he : entryFor (scanLines R.fa.lines.toList 0 [] []).1 (some ti, ret) = some e) :
    ∃ jl, R.L[jl]? = some (.label (.block l)) ∧ lineOffset R.L jl = e.pad := by
  have hlk : (scanLines R.fa.lines.toList 0 [] []).1.lookup l = some e.pad := by
    simp only [entryFor, handlersOf, hti, handlerEntry?] at he
    rcases hl with rfl | rfl <;> simp only [TryHandler.label] at he <;>
      cases hk : (scanLines R.fa.lines.toList 0 [] []).1.lookup l <;> simp [hk] at he <;>
      rw [← he]
  exact (labelOffsets_spec hR.lm _ _).mp (scanLines_labelOffsets hR.lm hlk)

theorem _root_.Backend.RepL.mono {af : AFunc} {own own' : Label → Bool} {LL : List Line} {s : Label} {j : Nat}
    (hown : ∀ l, own l = true → own' l = true) (h : RepL af own LL s j) : RepL af own' LL s j := by
  induction h with
  | here ho hj => exact .here (ho.imp id (hown _)) hj
  | skip ho hj _ ih => exact .skip (ho.imp id (hown _)) hj ih
  | fwd hf _ ih => exact .fwd hf ih

/-- A line representing a block is a label line. -/
theorem _root_.Backend.RepL.label {af : AFunc} {own : Label → Bool} {LL : List Line} {s : Label} {j : Nat}
    (h : RepL af own LL s j) : ∃ l', LL[j]? = some (.label l') := by
  induction h with
  | here _ hj => exact ⟨_, hj⟩
  | skip _ hj _ _ => exact ⟨_, hj⟩
  | fwd _ _ ih => exact ih

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The final code's block-label aliases are the emission plan's. -/
theorem emitFunc_alias {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    fa.alias = emitAlias k af := by
  unfold emitFunc at h
  cases hp : emitPre k af with
  | error e => rw [hp] at h; cases h
  | ok pre =>
    rw [hp] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      rfl

theorem lookup_append {α β : Type} [BEq α] (a : α) :
    ∀ (A B : List (α × β)), (A ++ B).lookup a = (A.lookup a).or (B.lookup a)
  | [], _ => by simp [List.lookup]
  | (k, v) :: A, B => by
    simp only [List.cons_append, List.lookup]
    split <;> simp [lookup_append a A B]

/-- A label line of `L` is found by `scanLines`. -/
theorem scanLines_lookup_some (x : Label) :
    ∀ (L : List Line) (off : Nat) (labs : List (Label × Nat)) (rets : List Nat),
      (Line.label (.block x) ∈ L ∨ (labs.lookup x).isSome) →
      ((scanLines L off labs rets).1.lookup x).isSome
  | [], _, labs, _, h => by simpa [scanLines] using h
  | ln :: L, off, labs, rets, h => by
    simp only [scanLines]
    apply scanLines_lookup_some x L
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · right; simp [labsAfter, List.lookup]
      · left; exact h
    · right
      unfold labsAfter
      split
      · simp only [List.lookup]; split <;> simp_all
      · exact h

/-- The alias entries `siteLabs` adds for label `l`: an alias `l ↦ x` of the final code whose
target `x` has a label offset. -/
theorem lookup_aliasLabs {labs : List (Label × Nat)} {l : Label} {off : Nat} :
    ∀ (al : List (Label × Label)),
      (al.filterMap (fun a => (labs.lookup a.2).map fun x => (a.1, x))).lookup l = some off →
      ∃ x, (l, x) ∈ al ∧ labs.lookup x = some off
  | [], h => by simp [List.lookup] at h
  | (l1, x1) :: al, h => by
    simp only [List.filterMap_cons] at h
    cases hx : labs.lookup x1 with
    | none =>
      simp only [hx, Option.map_none] at h
      obtain ⟨x, hm, hl⟩ := lookup_aliasLabs al h
      exact ⟨x, List.mem_cons_of_mem _ hm, hl⟩
    | some v =>
      simp only [hx, Option.map_some, List.lookup] at h
      split at h
      · rename_i he
        simp only [beq_iff_eq] at he
        subst he
        cases h
        exact ⟨x1, List.mem_cons_self, hx⟩
      · obtain ⟨x, hm, hl⟩ := lookup_aliasLabs al h
        exact ⟨x, List.mem_cons_of_mem _ hm, hl⟩

theorem lookup_aliasLabs_isSome {labs : List (Label × Nat)} {l x : Label}
    (hx : (labs.lookup x).isSome) :
    ∀ (al : List (Label × Label)), (l, x) ∈ al →
      ((al.filterMap (fun a => (labs.lookup a.2).map fun y => (a.1, y))).lookup l).isSome
  | [], h => by simp at h
  | (l1, x1) :: al, h => by
    simp only [List.filterMap_cons]
    cases hx1 : labs.lookup x1 with
    | none =>
      rcases List.mem_cons.1 h with e | hm
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [hx1] at hx; cases hx
      · simpa [hx1] using lookup_aliasLabs_isSome hx al hm
    | some v =>
      simp only [Option.map_some, List.lookup]
      split
      · rfl
      · rcases List.mem_cons.1 h with e | hm
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          rename_i hne
          simp at hne
        · exact lookup_aliasLabs_isSome hx al hm

/-- **The landing pad the call-site table gives a `try_call`'s first handler represents the
handler's block** (#553): the pad is the offset of a line that represents block `l` (`RepL`),
through `MachBuffer`'s label aliases (`aliasOk`) or the block's own label (`padsOk`). -/
theorem pad_rep {R : RL} (hR : R.Wf) {ti : TryInfo} {ret : Nat} {e : Unw.CallSiteEntry}
    {h : TryHandler} {hs : List TryHandler} (hti : ti.handlers = h :: hs) {l : Label}
    (hl : h = .tag 0 l ∨ h = .tag 1 l) {info : CallInfo} {lb : Label} {code : Array AInst}
    (hb : (lb, code) ∈ R.af.blocks.toList) (hc : AInst.inst (.tryCall info ti) ∈ code.toList)
    (he : entryFor (siteLabs R.fa) (some ti, ret) = some e) :
    ∃ jl, RepL R.af (planOwn R.fa.k R.af) R.L l jl ∧ lineOffset R.L jl = e.pad := by
  have hlk : (siteLabs R.fa).lookup l = some e.pad := by
    simp only [entryFor, handlersOf, hti, handlerEntry?] at he
    rcases hl with rfl | rfl <;> simp only [TryHandler.label] at he <;>
      cases hk : (siteLabs R.fa).lookup l <;> simp [hk] at he <;>
      rw [← he]
  obtain ⟨p, hp, -, -⟩ := emitFunc_ok hR.emit
  have hPL : planLines R.fa.k R.af = p.lines := by simp [planLines, hp]
  have hRL : R.L = relaxLines R.far p.lines := by rw [RL.L_plan hR, hPL]
  have hown : planOwn R.fa.k R.af = fun l => (segsTrust R.af p.segs p.outs p.lines).contains l := by
    simp [planOwn, hp]
  have hal : R.fa.alias = p.alias := by
    have := emitFunc_alias hR.emit
    rw [this, emitAlias, hp]
  obtain ⟨-, -, -, hali⟩ := emitPlan_spec hp
  -- a block label line `j` of the plan's lines whose offset `scanLines` finds is the pad
  have hoff : ∀ x j off, p.lines[j]? = some (.label (.block x)) →
      (scanLines R.fa.lines.toList 0 [] []).1.lookup x = some off →
      R.L[rix R.far p.lines j]? = some (.label (.block x)) ∧ lineOffset R.L (rix R.far p.lines j) = off := by
    intro x j off hj hx
    have hj' : R.L[rix R.far p.lines j]? = some (.label (.block x)) := by
      rw [hRL]; exact (relax_label hj).1
    obtain ⟨j', hj'', ho⟩ := (labelOffsets_spec hR.lm _ _).mp (scanLines_labelOffsets hR.lm hx)
    have := RL.label_unique hR hj'' hj'
    subst this
    exact ⟨hj', ho⟩
  -- an alias `l ↦ x`: `x`'s label line represents `l`
  have halias : ∀ x, (l, x) ∈ R.fa.alias → ∃ j, p.lines[j]? = some (.label (.block x)) ∧
      RepL R.af (planOwn R.fa.k R.af) R.L l (rix R.far p.lines j) := by
    intro x hx
    rw [hal] at hx
    have := hali _ hx
    unfold aliasOk at this
    split at this
    · rename_i j hj
      refine ⟨j, by simpa using blockLabelIdx_get hj, ?_⟩
      rw [hRL]
      exact RepL.relax _ (RepL.mono (fun _ h => by cases h) (repOn_repL this))
    · cases this
  unfold siteLabs at hlk
  rw [lookup_append] at hlk
  cases hA : (R.fa.alias.filterMap (fun a =>
      ((scanLines R.fa.lines.toList 0 [] []).1.lookup a.2).map fun x => (a.1, x))).lookup l with
  | some off =>
    rw [hA] at hlk
    simp only [Option.some_or, Option.some.injEq] at hlk
    subst hlk
    obtain ⟨x, hxm, hxo⟩ := lookup_aliasLabs _ hA
    obtain ⟨j, hj, hrep⟩ := halias x hxm
    exact ⟨_, hrep, (hoff x j _ hj hxo).2⟩
  | none =>
    rw [hA] at hlk
    simp only [Option.none_or] at hlk
    -- `padsOk`: the line the table names for `l` represents it
    have hpads := emitPlan_pads hp
    unfold padsOk at hpads
    simp only [List.all_eq_true] at hpads
    have hh := hpads _ hb _ hc
    simp only [List.all_eq_true] at hh
    have hh0 := hh h (by rw [hti]; exact List.mem_cons_self)
    have hlab : h.label = l := by rcases hl with rfl | rfl <;> rfl
    rw [hlab] at hh0
    cases hlo : p.alias.lookup l with
    | some x =>
      -- an alias of `l` whose target has a label line: `siteLabs` would have found it
      exfalso
      have hxm : (l, x) ∈ R.fa.alias := by
        rw [hal]
        exact mem_of_lookup hlo
      obtain ⟨j, hj, -⟩ := halias x hxm
      have hx := scanLines_lookup_some x R.fa.lines.toList 0 [] []
        (.inl (List.mem_of_getElem? (show R.L[rix R.far p.lines j]? = _ from by
          rw [hRL]; exact (relax_label hj).1)))
      have := lookup_aliasLabs_isSome hx _ hxm
      rw [hA] at this
      cases this
    | none =>
      simp only [hlo, Option.getD_none] at hh0
      split at hh0
      · rename_i j hj
        have hj' : p.lines[j]? = some (.label (.block l)) := by simpa using blockLabelIdx_get hj
        refine ⟨_, ?_, (hoff l j _ hj' hlk).2⟩
        rw [hRL, hown]
        exact RepL.relax _ (repOn_repL hh0)
      · cases hh0

/-- **A raising `try_call` on the machine, with the raising-call state's step facts**: the callee
raises, the personality installs the first handler's landing pad, and the machine is at the
landing-pad edge block with the payload in the call's defs, the raising-call state `RaiseXF`
(`RealizesTryRaiseP … R.GoodXUF`), for any semantics with `csemU`'s raising-`tryCall` clause
(`TryRaiseSem`: `R.semU`, `csemU`, the dead-cleanup chain's value semantics). -/
theorem realizes_tryCall_raiseUF {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU)
    (hT : LsdaAt R) (hpad : PadsNonzero R.af R.fa) (hsite : SiteAt R.toRL) :
    RealizesTryRaiseP R semU R.GoodXUF := by
  intro s b k allocs its m w vb info ti ops c' obj w2 hq _hA hvb hi hops hraise hm
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hcpc := callAt_of_q hR hq hvb hi tryCall_hcall
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins, hasgf,
    hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `try_call`'s allocated form
    -- is no `jump`
    rw [hvb] at hvbf
    cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hits
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    obtain ⟨ic, e, -⟩ := (assign_call_tryCall info regsf).2 ti (.jump xf) hasgf
    cases e
  cases hm with
  | @op _ _ _ _ _ _ vb' i2 ops2 outs outs' w' ctl m2 _ hvb' hi' hops2 hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops2; cases hops2
  -- a raising `try_call`'s control outcome is a jump to its first handler (`TryRaiseSem`), so
  -- its item is the block's last
  have hctl := (hsemT _ _ _ _ _ _ _ hsem hraise).2
  simp only [Prod.mk.injEq] at hctl
  obtain ⟨-, -, rfl⟩ := hctl
  cases hn with
  | @goto j0h st items' hk1 hsucc hitems =>
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hTq, htr,
    hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have huses := useVals_of_store hstat hm'
  rw [huses] at hraise
  have hopsC : (MInst.call info).operands = .ok ops := by
    rw [← operands_tryCall_call info ti]; exact hops
  have hsz0 := (checkStatic_facts hstat).1
  simp only [Array.size_map] at hsz0
  have hsem0 := hsem
  rw [huses] at hsem0
  have hgg := (hgot _ _ _ _).2 ti hsem0
  obtain ⟨hok, heq⟩ := hsemT _ _ _ _ _ _ _ hsem0 hraise
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, -⟩ := heq
  simp only [tryUOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hfirst, -⟩, hdefs01⟩, hp0⟩, hp1⟩ := hok
  -- the first handler
  obtain ⟨hd0, hs0, hfirstEq, l, hl⟩ : ∃ h hs, ti.handlers = h :: hs ∧
      ∃ l, h = .tag 0 l ∨ h = .tag 1 l := by
    revert hfirst
    rcases ti.handlers with _ | ⟨h, hs⟩
    · simp [firstHandlerOk]
    · intro hf
      refine ⟨h, hs, rfl, ?_⟩
      rcases h with ⟨_ | _ | n, l⟩ | l <;> simp_all [firstHandlerOk]
  -- the raising callee (the contract)
  have hsite0 : R.vc.CallSite info := ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩
  have hraiseU := hU.os info (.tryCall info ti) hsite0 (.inr ⟨ti, rfl⟩) s
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep cc wh ops regs i' w hops hstat hasg (hcpc regs i' rfl hasg) hst.world hst.align
    hst.err hgg
  obtain ⟨t, hUr, hW, hFK, herrt, hprogt, hoth, hkeep⟩ := hraiseU obj _ hraise
  obtain ⟨hstep1, hRX, hdesc, hxzr⟩ := RLU.stepU_q_raiseF hR hq hvb hi (.inr ⟨ti, rfl⟩) hUr
  -- the personality: the first handler's landing pad
  obtain ⟨j, x', hj, hpcj, -, hmem⟩ := hsite s b k _ [] m w vb _ info (some ti) hq hvb hi
    (.inr ⟨ti, rfl, rfl⟩)
  obtain ⟨sites, hcs, hlsda⟩ := hT
  obtain ⟨e, he, hpers⟩ := Unw.personality_callSite hcs hmem
  simp only [hpad ti _ e hmem he, ↓reduceIte] at hpers
  have hne : R.fb.words.toList ≠ [] := by
    obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hpb : progBase s = R.base := progBase_eq (by rw [hst.prog]; rfl) hne
  have hfit : lineOffset R.L j + 4 ≤ 2 ^ 64 := by
    have h1' := lineOffset_succ R.L j _ hj
    have h2' := lineOffset_le_size R.L (j + 1)
    have h3' := layout_sum hR.layout
    have h4' := hR.fit
    simp only [Line.size, RL.L] at h1' h2' h3' ⊢
    omega
  have hoff : (Arm.r .PC s + 4 - 1 - progBase s).toNat = lineOffset R.L j + 4 - 1 := by
    rw [hpcj, hpb]
    simp only [RL.pcOf]
    have : R.base + BitVec.ofNat 64 (lineOffset R.L j) + 4 - 1 - R.base =
        BitVec.ofNat 64 (lineOffset R.L j + 3) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (4 : BitVec 64).toNat = 4 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
      have := R.base.isLt
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hstepU : R.stepU s = Arm.w .PC (progBase s + BitVec.ofNat 64 e.pad)
      (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) := by
    rw [hstep1]
    apply Unw.unwindAt_install
    rw [hlsda, hoff]
    exact hpers
  -- the landing pad's line, which represents the first handler's block (`pad_rep`)
  obtain ⟨icT, hiT, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hmemT : ∃ lb code, (lb, code) ∈ R.af.blocks.toList ∧
      AInst.inst (.tryCall icT ti) ∈ code.toList := by
    obtain ⟨-, -, -, hblk⟩ := (lowerRFunc_ok hR.alloc).1
    obtain ⟨codeAll, hcodeAll, hab⟩ := hblk b vb items hvb hit
    rw [hsplit] at hcodeAll
    obtain ⟨cpre, crest, -, hcrest, rfl⟩ := itemsCode_append hcodeAll
    obtain ⟨c1a, c2a, hc1a, -, rfl⟩ := itemsCode_cons hcrest
    rw [show RAFrame.compute R.vc R.rf = R.fr from rfl, hc1] at hc1a
    cases hc1a
    have hc1eq : c1 = [AInst.inst i'] := by
      rcases hc1' with ⟨h, -, -⟩ | ⟨ds, h1, -⟩ | ⟨us, h1, -⟩
      · exact h
      · rw [hiT] at h1; cases h1
      · rw [hiT] at h1; cases h1
    refine ⟨vb.label, _, List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hab), ?_⟩
    rw [hc1eq, hiT]; simp
  obtain ⟨lbT, codeT, hbT, hcT⟩ := hmemT
  obtain ⟨jl, hrep, hjlo⟩ := pad_rep hR hfirstEq hl hbT hcT he
  obtain ⟨l', hjl⟩ := hrep.label
  -- the successor: the first handler's block
  have hnone : havocFrom (MInst.tryCall info ti) (.goto 0) = none := by
    simp [havocFrom, MInst.keptDefs, MInst.isBranch, MInst.normalDead, hfirstEq]
  obtain rfl := hho.2.1 hnone
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  have hti : t0 = .tryCall info ti := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ ((lowerRFunc_ok hR.alloc).2.2) hsucc
  have hvl : vs.label = l := by
    simp only [MInst.targets, hfirstEq, List.map_cons, List.cons_append,
      List.getElem?_cons_zero, Option.some.injEq] at hlj
    rcases hl with rfl | rfl <;> exact hlj.symm
  -- the machine after the install: the payload registers
  have hFK' : FrameKeep R.FK s (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) :=
    frameKeep_x01 ⟨hFK.1, fun a ha => hFK.2 a ⟨RL.FK_F ha, by rw [hst.sp]; exact RL.FK_not_below hR ha⟩⟩
  have hlenD : (payloadOuts (.call info) obj).length =
      ((ops.zip regs).toList.filter (·.1.isDef)).length := by
    rw [hlen, pairs_regs, List.filter_map, List.length_map]; rfl
  have hlen' : (payloadOuts (.call info) obj).length =
      ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length := hlen
  -- the defs: x0 := obj, x1 := 0
  have hdcons : ∀ o ∈ ops.toList, o.isDef = true → o.con = .fixed (.x 0) ∨ o.con = .fixed (.x 1) := by
    intro o ho hd
    have hmem : o.con ∈ defCons (.call info) := by
      simp only [defCons, hopsC]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, hd⟩)
    have := List.all_eq_true.mp hdefs01 _ hmem
    simpa using this
  have hdef : ∀ p ∈ defRegs ops regs (payloadOuts (.call info) obj),
      regVal (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) p.1.2 = p.2 := by
    intro p hp
    have hp2 : p.2 = (fun c => if c = .fixed (.x 0) then ofX obj else ofX 0) p.1.1.con := by
      refine mem_zip_filter_map Operand.isDef
        (fun o => if o.con = .fixed (.x 0) then ofX obj else ofX 0) (ops.zip regs).toList p ?_
      rw [zip_toList_map_fst ops regs hsz0]
      simpa [defRegs, payloadOuts, defCons, hopsC, List.map_map, Function.comp_def] using hp
    have hp1 : p.1 ∈ (ops.zip regs).toList ∧ p.1.1.isDef = true := by
      have := List.of_mem_zip hp
      exact List.mem_filter.mp this.1 |>.imp id (by simp)
    have hfx := (checkStatic_facts hstat).2.1 (p.1.1, Loc.reg p.1.2)
      (by rw [pairs_regs]; exact List.mem_map_of_mem hp1.1)
    have ho : p.1.1 ∈ ops.toList := by
      rw [← zip_toList_map_fst ops regs hsz0]; exact List.mem_map_of_mem hp1.1
    rcases hdcons _ ho hp1.2 with hc0 | hc1
    · have := hfx.2 _ hc0
      simp only [Loc.reg.injEq] at this
      rw [this, hp2]
      simp only [hc0, ite_true]
      exact regVal_x01_x0 t obj
    · have := hfx.2 _ hc1
      simp only [Loc.reg.injEq] at this
      rw [this, hp2]
      simp only [hc1, ite_false, Constraint.fixed.injEq, Reg.x.injEq, reduceCtorEq]
      exact regVal_x01_x1 t obj
  -- x0, x1 hold nothing kept live across the call
  have hnot01 : ∀ (r0 : Reg), payloadRegOk info ti r0 = true → ∀ r, r = r0 →
      (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
      r ∉ (MInst.tryCall info ti).clobbers → False := by
    intro r0 hpr r hr hnd hnc
    subst hr
    simp only [payloadRegOk, Bool.or_eq_true, List.contains_iff_mem] at hpr
    rcases hpr with hpr | hpr
    · exact hnc hpr
    · simp only [defCons, hopsC, List.mem_map, List.mem_filter] at hpr
      obtain ⟨o, ⟨ho, hd⟩, hc⟩ := hpr
      obtain ⟨p, hp, hpd, hpr⟩ := def_fixed_reg hstat ho hd hc
      exact hnd p hp hpd hpr
  obtain ⟨m3, hc3, hr3, hl3⟩ := operandsSound_post (s' := Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))
    hstat hm' hlen' hdef
    (fun r ha hnd hnc => by
      rw [regVal_x01 ha (fun e => hnot01 _ hp0 r e hnd hnc) (fun e => hnot01 _ hp1 r e hnd hnc)]
      exact hoth r ha hnd hnc)
    (fun r hr hcs => by
      have ha := calleeSaved_allocatable hcs
      have h0 : r ≠ .x 0 := by rintro rfl; simp [calleeSaved] at hcs <;> omega
      have h1 : r ≠ .x 1 := by rintro rfl; simp [calleeSaved] at hcs <;> omega
      rw [regVal_x01 ha h0 h1]
      exact hkeep r hr hcs)
  have hfr := R.frameOkK hR
  have hsp' : spOf (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) = R.spB := hFK'.1.trans hst.sp
  have hprog' : (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)).program = R.fb.program R.base := by
    rw [Arm.w_program, Arm.w_program, hprogt, hst.prog]
  have hstr : StRel R.toRL (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))
      (writeM m3 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
        (payloadOuts (.call info) obj)).filter (·.1.1.isLate))) w' := by
    refine ⟨fun l hl hL => ?_, sameWorld_x01 hW, err_x01 herrt, hprog', hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hFK'.2 a (.inl (.inr (.inr ha))),
      fun a ha => (hFK'.2 a (.inr ha)).trans (hst.gkeep a ha)⟩
    · cases l with
      | reg r => exact hr3 r (hl r rfl)
      | stack k' c =>
        rw [hl3 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hFK' hL (fun r h => by cases h)]
      | save r =>
        rw [hl3 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hFK' hL (fun r h => by cases h)]
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hFK'.2 _ (fplr_inF hR hframe k hk))
  refine ⟨1, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc3
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_⟩
  · simp only [iterN]
    rw [hstepU]
    refine q_entry hR hst0 hvs hitems (jl := jl) (by rw [hvl]; exact hrep) ?_ (hstr.pc _)
    rw [Arm.r_of_w_same, hpb]
    simp only [RL.pcOf, hjlo]
  · obtain rfl : i = 0 := by omega
    show R.GoodXUF s
    have hnext : R.NextOk s (R.stepU s) := by
      refine .inr (.inr (.inr ⟨jl, ?_, fun x tt h => by rw [hjl] at h; cases h⟩))
      rw [hstepU, Arm.r_of_w_same, hpb]
      simp only [RL.pcOf]
      rw [lineOffset_succ _ _ _ hjl, hjlo]
      simp [Line.size]
    have hexit : Unw.personality R.T.lsda (Arm.r .PC s + 4 - 1 - progBase s).toNat = .continue →
        ArmRet (xreg 30 R.s0) R.s0 (R.stepU s) ∧ (R.stepU s).program = R.fb.program R.base := by
      intro hc
      rw [hoff, hlsda, hpers] at hc
      cases hc
    have htsp : ∀ x d obj' t', R.AtLine s x →
        ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
        R.U.raise d s = some (obj', t') → spOf t' = R.spB := by
      intro x d obj' t' hx hd hr'
      obtain rfl := hdesc x d hx hd
      rw [hUr] at hr'
      cases hr'
      exact hFK.1.trans hst.sp
    exact .inr ⟨hRX, hnext, hexit, htsp, fun x hx => ⟨hxzr x hx, hst.code⟩,
      ⟨.tryCall info ti, info, hsite0, .inr ⟨ti, rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
        fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
        obj, _, hops, hstat, hasg, hcpc regs i' rfl hasg, hst.world, hst.align, hst.err, hgg,
        hraise⟩⟩

/-- **A raising `try_call` on the machine**: the callee raises, the personality installs the
first handler's landing pad, and the machine is at the landing-pad edge block with the payload in
the call's defs (`RealizesTryRaise`), for any semantics with `csemU`'s raising-`tryCall` clause
(`TryRaiseSem`: `R.semU`, `csemU`, the dead-cleanup chain's value semantics). -/
theorem realizes_tryCall_raiseU {R : RLU} (hR : R.Wf) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hsemT : TryRaiseSem R.XR semU) (hgot : GotSem R.gv R.X semU)
    (hT : LsdaAt R) (hpad : PadsNonzero R.af R.fa) (hsite : SiteAt R.toRL) :
    RealizesTryRaise R semU :=
  (realizes_tryCall_raiseUF hR hU hsemT hgot hT hpad hsite).mono fun _ h => h.goodXU

/-! ## Discharging `SiteAt` and `PadsNonzero` -/

/-- **`SiteAt` from the check of the last block's calls** (`q_callSite`, `q_callSite_last`). -/
theorem siteAt_of_check {R : RL} (hR : R.Wf) (h : lastCallsOk R.af R.fa = true) : SiteAt R := by
  intro s b k allocs its m w vb i info c hq hvb hi hc
  cases hb : R.af.blocks[b + 1]? with
  | none => exact q_callSite_last hR hq hvb hi hc hb h
  | some p => exact q_callSite hR hq hvb hi hc (by rw [hb]; rfl)

/-- The check that the landing pads of the emitted call-site table are at non-zero offsets
(decidable, on `af` and its final code `fa`; entries looked up as `callSites` does, `siteLabs`). -/
def padsNonzeroB (af : AFunc) (fa : FnAsm) : Bool :=
  let r := scanLines fa.lines.toList 0 [] []
  (af.calls.zip r.2).all fun p => match p.1, entryFor (siteLabs fa) p with
    | some _, some e => e.pad != 0
    | _, _ => true

theorem padsNonzero_of_check {af : AFunc} {fa : FnAsm} (h : padsNonzeroB af fa = true) :
    PadsNonzero af fa := by
  intro ti ret e hm he
  have := List.all_eq_true.mp h _ hm
  simp only [he] at this
  simpa using this

/-! ## Non-vacuity -/

namespace UTryWitness

open Backend.Proof.UnwindTables.Witness in
/-- S10c's witness function (a `try_call` whose catch handler's landing pad is at offset 32)
passes both checks: its call-site bridge (`siteAt_of_check`) and its landing pads
(`padsNonzero_of_check`) are discharged. -/
theorem checks : padsNonzeroB af fa = true ∧ lastCallsOk af fa = true := by decide +kernel

open Backend.Proof.UnwindTables.Witness in
theorem pads : PadsNonzero af fa := padsNonzero_of_check checks.1

open Backend.Proof.UnwindTables.Witness in
/-- The check is not vacuous there: the function's one call is a `try_call` whose entry has
landing pad 32. -/
theorem entry :
    af.calls.zip (scanLines fa.lines.toList 0 [] []).2 = [(some ⟨1, [.tag 1 2], false, 0⟩, 20)] ∧
      entryFor (scanLines fa.lines.toList 0 [] []).1 (some ⟨1, [.tag 1 2], false, 0⟩, 20) =
        some ⟨19, 1, 32, 1⟩ := by
  decide +kernel

end UTryWitness

end Backend.Proof
