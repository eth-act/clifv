module

public import FV.Concurrency.VCodeAddrAtomic

@[expose] public section

/-!
# The events of a successful `csem` step avoid the frame (T2h, #311, layer 2a)

**`cEvs_avoid`**: when `csem F` steps (returns `some`), every event of its precise footprint
`VCodeThread.cEvs` lies outside the frame set `F`. `csem` checks `F` only on `MInst.accesses`
(`AccessOk`) and on the LL/SC loops' address, so this is the statement "every event address lies
within `MInst.accesses`" (finding 3 of `docs/plans/atomics.md` §3e):

* straight-line memory forms (`load`/`store`/`fpuLoad`/`fpuStore` at every covered addressing mode,
  `loadAcquire`/`storeRelease`): their canonical run's one event is at the access's address, of its
  size (`VCodeAddr.load_lines_evs` …, `ldar_evs`, `stlr_evs`), and `straightSem` checks the access
  (`straight_avoid_of`); `fence`'s barrier event has size 0; every other straight-line form has
  no event (`VCodeEvents.straightEvs_kinds`);
* the LL/SC loops: every event is at x25, which holds the address operand, of the access size
  (`rmwBody_evs`, `casHead_evs`, `casStore_evs`), and `loopSem` checks that access;
* the other control forms have no events.

With `F` the complement of a CLIF event's bytes, this places every VCode event of a statement in
that event's bytes (the plan of layer 2).
-/

namespace Concurrency.VCodeAddr

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code

/-- Every event avoids `F` (`RegallocOperands.Avoids` of its bytes). -/
def EvsAvoid (F : BitVec 64 → Prop) (evs : List Ev) : Prop := ∀ e ∈ evs, Avoids F e.n e.addr

theorem evsAvoid_nil (F : BitVec 64 → Prop) : EvsAvoid F [] := fun _ h => nomatch h

theorem evsAvoid_append {F : BitVec 64 → Prop} {a b : List Ev} (ha : EvsAvoid F a)
    (hb : EvsAvoid F b) : EvsAvoid F (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact ha e h
  · exact hb e h

theorem evsAvoid_of_atA {F : BitVec 64 → Prop} {a : BitVec 64} {n : Nat} {evs : List Ev}
    (h : AtA a n evs) (hav : Avoids F n a) : EvsAvoid F evs := by
  intro e he
  obtain ⟨h1, h2⟩ := h e he
  rw [h1, h2]; exact hav

theorem At.toA {k : AKind} {a : BitVec 64} {n : Nat} {evs : List Ev} (h : At k a n evs) :
    AtA a n evs := fun e he => ⟨(h e he).2.1, (h e he).2.2⟩

/-! ## Alignment of the canonical state -/

theorem r31_foldl : ∀ (ps : List (Reg × CV)) (s : ArmState),
    (∀ p ∈ ps, ∀ n, p.1 = .x n → rnum n ≠ 31#5) →
    Arm.r (.GPR 31#5) (ps.foldl (fun s p => setReg s p.1 p.2) s) = Arm.r (.GPR 31#5) s
  | [], _, _ => rfl
  | p :: ps, s, h => by
    simp only [List.foldl_cons]
    rw [r31_foldl ps _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    obtain ⟨r, v⟩ := p
    cases r with
    | x n =>
      have hn := h _ List.mem_cons_self n rfl
      simp only [setReg]
      rw [Arm.r_of_w_different (by simp [Ne.symm hn])]
    | v n => simp only [setReg]; rw [Arm.r_of_w_different (by simp)]
    | _ => rfl

/-- **The canonical state is aligned** when the world is and no use register is `x31`. -/
theorem spAlign_placeUses (ops : Array Operand) (regs : Array Reg) (uses : List CV)
    {w : ArmState} (hal : CheckSPAlignment w)
    (h : ∀ q ∈ (ops.zip regs).toList, ∀ n, q.2 = .x n → rnum n ≠ 31#5) :
    CheckSPAlignment (placeUses ops regs uses w) := by
  have e : Arm.r (.GPR 31#5) (placeUses ops regs uses w) = Arm.r (.GPR 31#5) w := by
    unfold placeUses
    refine r31_foldl _ w fun p hp n hn => ?_
    obtain ⟨r, v⟩ := p
    have hr := (List.of_mem_zip hp).1
    simp only [List.mem_map, List.mem_filter] at hr
    obtain ⟨q, ⟨hq, -⟩, rfl⟩ := hr
    exact h q hq n hn
  simpa [CheckSPAlignment, Arm.read_gpr, e] using hal

/-! ## Straight-line forms -/

theorem accessOk_of_straightSem {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst}
    {uses : List CV} {w : ArmState} {ops : Array Operand} {r : List CV × ArmState × Ctl}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hs : straightSem F ctx i uses w = some r) :
    AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) := by
  unfold straightSem at hs
  simp only [hops, hic] at hs
  split at hs
  · assumption
  · cases hs

/-- **A straight-line form with one access**: when every run of its canonical allocation's lines
has its events at the access (`A s`, `n` bytes), a successful `straightSem` step's events avoid
`F`. -/
theorem straight_avoid_of {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {r : List CV × ArmState × Ctl}
    {A : ArmState → BitVec 64} {n : Nat}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hacc_eq : ∀ s, ic.accesses ctx s = [(A s, n)])
    (hev : ∀ s, CheckSPAlignment s → ∀ ls (ps : Backend.PState), ic.lines ctx {} = .ok (ls, ps) →
      AtA (A s) n (linesEvs env0 ls s))
    (hal : CheckSPAlignment (placeUses ops (canonRegs ops) uses w))
    (hs : straightSem F ctx i uses w = some r) : EvsAvoid F (straightEvs ctx i uses w) := by
  have hacc := accessOk_of_straightSem hops hic hs
  unfold straightEvs
  simp only [hops, hic]
  split
  · rename_i ls ps hls
    refine evsAvoid_of_atA (hev _ hal ls ps hls) ?_
    exact hacc _ (by rw [hacc_eq]; exact List.mem_singleton_self _)
  · exact evsAvoid_nil F

/-- A straight-line form whose events have size 0 (`fence`). -/
theorem straight_avoid_zero {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hev : ∀ s ls (ps : Backend.PState), ic.lines ctx {} = .ok (ls, ps) →
      ∀ e ∈ linesEvs env0 ls s, e.n = 0) :
    EvsAvoid F (straightEvs ctx i uses w) := by
  unfold straightEvs
  simp only [hops, hic]
  split
  · rename_i ls ps hls
    intro e he k hk
    rw [hev _ ls ps hls e he] at hk
    exact absurd hk (Nat.not_lt_zero k)
  · exact evsAvoid_nil F

theorem straightEvs_nil {ctx : FnCtx} {i : MInst} (h : akinds i = []) (uses : List CV)
    (w : ArmState) : straightEvs ctx i uses w = [] := by
  have := straightEvs_kinds ctx i uses w
  rw [h, List.sublist_nil, List.map_eq_nil_iff] at this
  exact this

/-- The lines of a one-line form. -/
theorem lines_one {ctx : FnCtx} {i : MInst} {l : Line} {ls : List Line} {ps : Backend.PState}
    (h1 : MInst.lines ctx i {} = .ok ([l], {})) (h : MInst.lines ctx i {} = .ok (ls, ps)) :
    ls = [l] := by
  rw [h1] at h
  cases h; rfl

/-- **The canonical state is aligned** (no canonical register is `x31`). -/
theorem spAlign_canon (ops : Array Operand) (uses : List CV) {w : ArmState}
    (hal : CheckSPAlignment w) (h : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5) :
    CheckSPAlignment (placeUses ops (canonRegs ops) uses w) :=
  spAlign_placeUses _ _ _ hal fun q hq n hn =>
    h q.2 (by have := (List.of_mem_zip (by simpa [Array.toList_zip] using hq)).2; simpa using this)
      n hn

/-- The canonical registers of a concrete form are not `x31`. -/
syntax "canon_regs" : tactic
macro_rules
  | `(tactic| canon_regs) => `(tactic| (
    simp [canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use, List.range_succ]
    try decide))

/-- The canonical addressing mode of a covered form is a `MemMode`. -/
syntax "mm_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mm_tac) => `(tactic| (
    simp [MemMode, FinalAM, BaseOk, IdxOk, canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use,
      List.range_succ]
    try first | exact hm | (simpa [extOk] using hm) | omega))

/-! ## The memory forms -/

theorem load_avoid_of {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} (hop : op ≠ .fpuLoad128)
    {d : Nat} {m : AMode} {fl : Clif.MemFlags} {uses : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.load op (.vreg d .int) m fl) uses w = some r)
    (mc : AMode) (hmc : MemMode op.bytes mc) (ops : Array Operand)
    (hops : (MInst.load op (.vreg d .int) m fl).operands = .ok ops)
    (hic : (MInst.load op (.vreg d .int) m fl).assign (canonRegs ops) = .ok (.load op (.x 0) mc fl))
    (hr : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5) :
    EvsAvoid F (straightEvs ctx (.load op (.vreg d .int) m fl) uses w) :=
  straight_avoid_of hops hic (fun _ => rfl)
    (fun s hs' ls ps hl => (load_lines_evs ctx env0 op hop (d := 0) (by decide) fl hmc s hs' hl).toA)
    (spAlign_canon ops uses hal hr) hs

theorem store_avoid_of {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} (hop : op ≠ .fpuStore128)
    {d : Nat} {m : AMode} {fl : Clif.MemFlags} {uses : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.store op (.vreg d .int) m fl) uses w = some r)
    (mc : AMode) (hmc : MemMode op.bytes mc) (ops : Array Operand)
    (hops : (MInst.store op (.vreg d .int) m fl).operands = .ok ops)
    (hic : (MInst.store op (.vreg d .int) m fl).assign (canonRegs ops) = .ok (.store op (.x 0) mc fl))
    (hr : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5) :
    EvsAvoid F (straightEvs ctx (.store op (.vreg d .int) m fl) uses w) :=
  straight_avoid_of hops hic (fun _ => rfl)
    (fun s hs' ls ps hl => (store_lines_evs ctx env0 op hop (d := 0) (by decide) fl hmc s hs' hl).toA)
    (spAlign_canon ops uses hal hr) hs

theorem fpuLoad_avoid_of {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} (hsz : FpSz sz)
    {d : Nat} {m : AMode} {fl : Clif.MemFlags} {uses : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.fpuLoad sz (.vreg d .float) m fl) uses w = some r)
    (mc : AMode) (hmc : MemMode sz.bytes mc) (ops : Array Operand)
    (hops : (MInst.fpuLoad sz (.vreg d .float) m fl).operands = .ok ops)
    (hic : (MInst.fpuLoad sz (.vreg d .float) m fl).assign (canonRegs ops) =
      .ok (.fpuLoad sz (.v 0) mc fl))
    (hr : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5) :
    EvsAvoid F (straightEvs ctx (.fpuLoad sz (.vreg d .float) m fl) uses w) :=
  straight_avoid_of hops hic (fun _ => rfl)
    (fun s hs' ls ps hl => (fpuLoad_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl hmc s hs' hl).toA)
    (spAlign_canon ops uses hal hr) hs

theorem fpuStore_avoid_of {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} (hsz : FpSz sz)
    {d : Nat} {m : AMode} {fl : Clif.MemFlags} {uses : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.fpuStore sz (.vreg d .float) m fl) uses w = some r)
    (mc : AMode) (hmc : MemMode sz.bytes mc) (ops : Array Operand)
    (hops : (MInst.fpuStore sz (.vreg d .float) m fl).operands = .ok ops)
    (hic : (MInst.fpuStore sz (.vreg d .float) m fl).assign (canonRegs ops) =
      .ok (.fpuStore sz (.v 0) mc fl))
    (hr : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5) :
    EvsAvoid F (straightEvs ctx (.fpuStore sz (.vreg d .float) m fl) uses w) :=
  straight_avoid_of hops hic (fun _ => rfl)
    (fun s hs' ls ps hl => (fpuStore_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl hmc s hs' hl).toA)
    (spAlign_canon ops uses hal hr) hs

theorem load_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {rd : Reg} {m : AMode}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.load op rd m fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.load op rd m fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.load op rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact load_avoid_of hop hal hs _ (by mm_tac) _ rfl rfl (by canon_regs)

theorem store_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {rd : Reg} {m : AMode}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.store op rd m fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.store op rd m fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.store op rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact store_avoid_of hop hal hs _ (by mm_tac) _ rfl rfl (by canon_regs)

theorem fpuLoad_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.fpuLoad sz rd m fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.fpuLoad sz rd m fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.fpuLoad sz rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact fpuLoad_avoid_of hsz hal hs _ (by mm_tac) _ rfl rfl (by canon_regs)

theorem fpuStore_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.fpuStore sz rd m fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.fpuStore sz rd m fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.fpuStore sz rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact fpuStore_avoid_of hsz hal hs _ (by mm_tac) _ rfl rfl (by canon_regs)

theorem loadAcquire_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.loadAcquire ty rt rn fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.loadAcquire ty rt rn fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.loadAcquire ty rt rn fl) uses w) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_avoid_of (ic := .loadAcquire ty (.x 1) (.x 0) fl) rfl rfl (fun _ => rfl)
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact ldar_evs hfo env0 _ s)
    (spAlign_canon _ uses hal (by canon_regs)) hs

theorem storeRelease_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} {uses : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (hfo : FormOk ctx (.storeRelease ty rt rn fl) = true) (hal : CheckSPAlignment w)
    (hs : straightSem F ctx (.storeRelease ty rt rn fl) uses w = some r) :
    EvsAvoid F (straightEvs ctx (.storeRelease ty rt rn fl) uses w) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_avoid_of (ic := .storeRelease ty (.x 1) (.x 0) fl) rfl rfl (fun _ => rfl)
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact stlr_evs hfo env0 _ s)
    (spAlign_canon _ uses hal (by canon_regs)) hs

theorem fence_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {uses : List CV} {w : ArmState} :
    EvsAvoid F (straightEvs ctx .fence uses w) :=
  straight_avoid_zero rfl rfl (fun s ls ps hl => by rw [lines_one rfl hl]; exact fence_evs env0 _ s)

/-- **The events of a successful straight-line step avoid the frame.** -/
theorem straightEvs_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} {uses : List CV}
    {w : ArmState} {r : List CV × ArmState × Ctl} (hfo : FormOk ctx i = true)
    (hal : CheckSPAlignment w) (hs : straightSem F ctx i uses w = some r) :
    EvsAvoid F (straightEvs ctx i uses w) := by
  by_cases hk : akinds i = []
  · rw [straightEvs_nil hk]; exact evsAvoid_nil F
  · cases i with
    | load => exact load_avoid hfo hal hs
    | store => exact store_avoid hfo hal hs
    | fpuLoad => exact fpuLoad_avoid hfo hal hs
    | fpuStore => exact fpuStore_avoid hfo hal hs
    | loadAcquire => exact loadAcquire_avoid hfo hal hs
    | storeRelease => exact storeRelease_avoid hfo hal hs
    | fence => exact fence_avoid
    | _ => first | exact absurd rfl hk | (simp [FormOk] at hfo)

/-! ## The LL/SC loops -/

open Classical in
theorem loopSem_some {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : loopSem F ty a body regs uses defs w = some r) :
    AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧ Arm.r .ERR w = .None ∧
      execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) = some r.2.1 := by
  unfold loopSem at h
  split at h
  · rename_i hc
    refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
    split at h
    · rename_i t' ht
      split at h
      · cases h; exact ht
      · cases h
    · cases h
  · cases h

theorem r25_two (u x : CV) (w : ArmState) :
    Arm.r (.GPR 25#5) (([Reg.x 25, .x 26].zip [u, x]).foldl (fun s p => setReg s p.1 p.2) w) =
      lo64 u := by
  simp [setReg, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

theorem r25_three (u e x : CV) (w : ArmState) :
    Arm.r (.GPR 25#5) (([Reg.x 25, .x 26, .x 28].zip [u, e, x]).foldl
      (fun s p => setReg s p.1 p.2) w) = lo64 u := by
  simp [setReg, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

theorem err_two (u x : CV) (w : ArmState) :
    Arm.r .ERR (([Reg.x 25, .x 26].zip [u, x]).foldl (fun s p => setReg s p.1 p.2) w) =
      Arm.r .ERR w := by
  simp [setReg, rnum, Arm.r_of_w_different]

theorem err_three (u e x : CV) (w : ArmState) :
    Arm.r .ERR (([Reg.x 25, .x 26, .x 28].zip [u, e, x]).foldl
      (fun s p => setReg s p.1 p.2) w) = Arm.r .ERR w := by
  simp [setReg, rnum, Arm.r_of_w_different]

/-- **The events of a successful `csem` step avoid the frame `F`** (every instruction but calls;
an error-free world; a straight-line form covered by `csem`'s canonical run on an aligned
world, as `ifoot_csem`). -/
theorem cEvs_avoid {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} {r : List CV × ArmState × Ctl} (he : Arm.r .ERR w = .None)
    (hst : i.isCtl = false → csemWF ctx i uses = true ∧ CheckSPAlignment w)
    (h : csem F ctx X i uses w = some r) : EvsAvoid F (cEvs F ctx i uses w) := by
  unfold cEvs
  by_cases hc : i.isCtl = true
  · simp only [hc, ite_true]
    cases i with
    | atomicRmwLoop ty op fl a b c d e =>
      rcases uses with _ | ⟨u, _ | ⟨x, _ | ⟨y, t⟩⟩⟩ <;> try exact evsAvoid_nil F
      simp only [csem, he, ite_true] at h
      obtain ⟨hty, hav, herr, -⟩ := loopSem_some h
      refine evsAvoid_of_atA ?_ hav
      have := rmwBody_evs hty op fl env0
        (([Reg.x 25, .x 26].zip [u, x]).foldl (fun s p => setReg s p.1 p.2) w)
        (by rw [err_two]; exact herr)
      rwa [r25_two] at this
    | atomicCasLoop ty fl a b c d e =>
      rcases uses with _ | ⟨u, _ | ⟨ex, _ | ⟨x, _ | ⟨y, t⟩⟩⟩⟩ <;> try exact evsAvoid_nil F
      simp only [csem, he, ite_true] at h
      unfold casEvs
      cases hL : loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, ex, x]
          [.x 27, .x 24] w with
      | none => rw [hL] at h; cases h
      | some r1 =>
        obtain ⟨outs, t1, c1⟩ := r1
        obtain ⟨hty, hav, herr, hrun⟩ := loopSem_some hL
        have hhead : EvsAvoid F (loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
            [u, ex, x] w) := by
          refine evsAvoid_of_atA ?_ hav
          have := casHead_evs hty fl env0
            (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
            (by rw [err_three]; exact herr)
          rwa [r25_three] at this
        simp only [hL]
        by_cases hne : Arm.ConditionHolds Cond.ne.bits t1 = true
        · rw [if_pos hne]; exact hhead
        · rw [if_neg hne]
          refine evsAvoid_append hhead (evsAvoid_of_atA ?_ hav)
          obtain ⟨t', ht', -, -, hfr, -⟩ := casHead_spec hty fl env0
            (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
            (by rw [err_three]; exact herr)
          rw [ht'] at hrun
          simp only [Option.some.injEq] at hrun
          have h25 : Arm.r (.GPR 25#5) t1 = lo64 u := by
            rw [← hrun, hfr (.GPR 25#5) (by simp) (by simp) (by simp), r25_three]
          have := casStore_evs hty fl env0 t1
          rw [h25] at this
          exact this
    | _ =>
      first
      | exact evsAvoid_nil F
      | (simp only [MInst.isCtl] at hc; cases hc)
  · have hc' : i.isCtl = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    obtain ⟨hwf, hal⟩ := hst hc'
    rw [csem_of_wf hc' hwf he hal] at h
    have hfo : FormOk ctx i = true := by
      simp only [csemWF, Bool.and_eq_true] at hwf
      exact hwf.1
    exact straightEvs_avoid hfo hal h

end Concurrency.VCodeAddr
