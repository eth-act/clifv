import FV.Concurrency.ArmAllocMove

/-!
# Precise Arm runs of compiled code, forward (T2k, #311)

Layer 4b is backward (every precise run is realized); its non-vacuity on compiled code needs
precise runs that exist. They are built forward from the register-level relation `Q`, reading the
thread's own bytes (so `OkPriv` holds):

* `step_fwd`: at an unhooked instruction line that is no store exclusive, the one-step precise
  run with the single-core step's events (`exists_prun_line` on the thread's own memory);
* `prun_fwd`: through straight-line lines (`LinesAt`), the precise run with the single-core
  events, step by step;
* `move_fwd`, `moves_fwd`: through a move item (`move_lines`), and through a list of moves at the
  head of a block: `Q` after them, every event private, of the kinds of the moves' lines;
* `q_head`: at a `Q` state, the first line of the remaining items' code is at the pc
  (`codeLinesE_head_fence`: a `fence` first, `dmb ish`).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents

/-- **One precise step at an unhooked line** (no store exclusive), reading the thread's own
memory: its label is the single-core step's events, its state the single-core step's. -/
theorem step_fwd {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t))
    (hh : x.hooked = false) (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.pcOf j) (herr : Arm.r .ERR s = .None) (hns : NoStx s) (mon : Mon) :
    ∃ t1 : ArmState × Mon, PRun Policy.arm R.step (OkPriv R) (s, mon) [⟨stepEvs s, false⟩] t1 ∧
      t1.1 = R.step s := by
  obtain ⟨a0, ha0, -, -, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh
    hprog hpc herr
  obtain ⟨a, t'', ha, -, hr⟩ := exists_prun_line hR hj hh hprog hpc herr (fun a' ha' rel rs rn hc => by
    rw [show R.envOf j = ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ from rfl, ha0] at ha'
    cases ha'
    exact hns rel rs rn (by rw [cls_of_decode hdec]; exact hc)) mon s.mem
  rw [setMem_self] at hr
  cases hr with
  | cons hs hp _ hr' =>
    cases hr'
    obtain ⟨h1, -, -⟩ := tstep_own hs hp (ArmPrecise.agrees_stepEvs s) rfl
    exact ⟨_, .cons hs hp (fun e he hR' _ => ArmPrecise.agrees_stepEvs s e he hR') .nil, h1⟩

/-- **The precise run through straight-line lines** (no store exclusive), reading the thread's
own memory: the single-core run, its labels the single-core events. -/
theorem prun_fwd {R : RL} (hR : R.Wf) :
    ∀ {ls1 : List Line} {j : Nat} {s s' : ArmState}, LinesAt R j ls1 s s' →
      (∀ i < ls1.length, NoStx (iterN R.step i s)) →
      ∀ mon, ∃ t' : ArmState × Mon, PRun Policy.arm R.step (OkPriv R) (s, mon)
        ((segEvs R.step ls1.length s).map fun e => ⟨e, false⟩) t' ∧ t'.1 = s'
  | [], _, s, s', h, _, mon => by
    have : s' = s := by have := h.run; simp [execLines] at this; exact this.symm
    subst this
    exact ⟨(s', mon), .nil, rfl⟩
  | .label _ :: _, _, _, _, h, _, _ => by have := h.run; simp [execLines] at this
  | .word _ _ :: _, _, _, _, h, _, _ => by have := h.run; simp [execLines] at this
  | .data _ :: _, _, _, _, h, _, _ => by have := h.run; simp [execLines] at this
  | .ins x t :: rest, j, s, s', h, hns, mon => by
    have hj : R.fa.lines.toList[j]? = some (.ins x t) := by simpa using h.at_ 0 _ rfl
    have hh := h.hook x t List.mem_cons_self
    obtain ⟨a, ha, hstep, -, -⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh
      h.prog h.pc h.err
    obtain ⟨⟨s1, mon1⟩, r1, hs1⟩ := step_fwd hR hj hh h.prog h.pc h.err (hns 0 (by simp)) mon
    simp only at hs1
    have hrun := h.run
    simp only [execLines, ha] at hrun
    split at hrun
    · rename_i hpc'
      have hoff := lineOffset_succ R.fa.lines.toList j _ hj
      simp only [Line.size] at hoff
      have hs1' : s1 = Arm.exec_inst a s := hs1.trans hstep
      subst hs1'
      have hns' : ∀ i < rest.length, NoStx (iterN R.step i (Arm.exec_inst a s)) := fun i hi => by
        have := hns (i + 1) (by simp; omega)
        simp only [iterN] at this
        rwa [show R.step s = Arm.exec_inst a s from hstep] at this
      have hseg : segEvs R.step (rest.length + 1) s =
          stepEvs s :: segEvs R.step rest.length (Arm.exec_inst a s) := by
        simp only [segEvs]; rw [show R.step s = Arm.exec_inst a s from hstep]
      cases rest with
      | nil =>
        simp only [execLines, Option.some.injEq] at hrun
        subst hrun
        refine ⟨(Arm.exec_inst a s, mon1), ?_, rfl⟩
        have e1 : segEvs R.step 1 s = [stepEvs s] := rfl
        simpa [e1] using r1
      | cons ln ls' =>
        have h1 := h.inter 1 (by omega) (by simp) (Arm.exec_inst a s)
          (by simp [execLines, ha, hpc'])
        have hrest : LinesAt R (j + 1) (ln :: ls') (Arm.exec_inst a s) s' := {
          at_ := fun k ln' hk => by
            have := h.at_ (k + 1) ln' (by simpa using hk)
            rwa [show j + (k + 1) = j + 1 + k by omega] at this
          hook := fun x' t' hm' => h.hook x' t' (List.mem_cons_of_mem _ hm')
          prog := by rw [h1.2, h.prog]
          pc := by
            rw [hpc', h.pc, hoff, BitVec.add_assoc]
            congr 1
            apply BitVec.eq_of_toNat_eq
            simp
          err := h1.1
          inter := fun k hk0 hk s2 hs2 => by
            have := h.inter (k + 1) (by omega) (by simp at hk ⊢; omega) s2
              (by simp [execLines, ha, hpc']; simpa [hoff] using hs2)
            exact ⟨this.1, by rw [this.2, h1.2]⟩
          run := by simpa [hoff] using hrun }
        obtain ⟨t', r2, ht'⟩ := prun_fwd hR hrest hns' mon1
        refine ⟨t', ?_, ht'⟩
        rw [List.length_cons, hseg, List.map_cons]
        cases r1 with
        | cons hs hp ho r1' =>
          cases r1'
          exact .cons hs hp ho r2
    · cases hrun

/-- The events of a segment of single-core steps, as precise labels. -/
theorem evTr_seg (f : ArmState → ArmState) (n : Nat) (s : ArmState) :
    evTr ((segEvs f n s).map fun e => (⟨e, false⟩ : Lab)) = segEvs f n s := by
  simp [evTr, Function.comp_def]

/-- **Through a move item** other than a callee restore (`move_lines`): the precise run (reading
the thread's own bytes) through the move's lines, `Q` at the next item; its events are private
and of the kinds of the move's lines. -/
theorem move_fwd {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState} (hq : Q R s (MvC b src dst its m w))
    (mon : Mon) (hns : src.isSave = false) :
    ∃ (ls : List Lab) (t' : ArmState × Mon), PRun Policy.arm R.step (OkPriv R) (s, mon) ls t' ∧
      Q R t'.1 (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∃ code ls1, R.fr.moveInsts src dst = .ok code ∧
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) ∧
        ∀ l ∈ ls, ∀ e ∈ l.evs, R.F e.addr ∧ e.k ∈ kinds ls1 := by
  obtain ⟨j, ls1, s', code, hc, hcl, hlat, hq', hpriv⟩ := move_lines hR hq hns
  obtain ⟨t', r, ht'⟩ := prun_fwd hR hlat (fun i hi => (hpriv i hi).2) mon
  refine ⟨_, t', r, by rw [ht']; exact hq', code, ls1, hc, hcl {}, fun l hl e he => ?_⟩
  obtain ⟨ev, hev, rfl⟩ := List.mem_map.mp hl
  obtain ⟨i, hi, rfl⟩ := mem_segEvs hev
  refine ⟨(hpriv i hi).1 e he, ?_⟩
  have hm : e ∈ (segEvs R.step ls1.length s).flatten :=
    List.mem_flatten.2 ⟨_, stepEvs_mem_segEvs hi, he⟩
  rw [hlat.seg hR] at hm
  exact (linesEvs_kinds _ ls1 s).subset (List.mem_map_of_mem hm)

/-- **Through a list of moves at the head of the items** (no callee restore among them): `Q`
after them, every event private and of a kind `P` admits (`P` holding at the kinds of each
move's lines). -/
theorem moves_fwd {R : RL} (hR : R.Wf) (P : AKind → Prop) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV) (mon : Mon),
      Q R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      (∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → ∀ K ∈ kinds ls1, P K) →
      (∀ p ∈ mvs, p.1.isSave = false) →
      ∃ (ls : List Lab) (t' : ArmState × Mon) (m' : Loc → CV),
        PRun Policy.arm R.step (OkPriv R) (s, mon) ls t' ∧ Q R t'.1 (.run ⟨b, its, m', w⟩) ∧
        ∀ l ∈ ls, ∀ e ∈ l.evs, R.F e.addr ∧ P e.k
  | [], its, s, m, mon, hq, _, _ => ⟨[], (s, mon), m, .nil, hq, fun _ h => absurd h List.not_mem_nil⟩
  | p :: mvs, its, s, m, mon, hq, hK, hns => by
    obtain ⟨ls, t1, r1, hq1, code, ls1, hc, hcl, hev⟩ := move_fwd hR hq mon (hns p List.mem_cons_self)
    obtain ⟨ls', t2, m2, r2, hq2, hev2⟩ := moves_fwd hR P mvs its t1.1 _ t1.2 hq1
      (fun p' hp' => hK p' (List.mem_cons_of_mem _ hp')) (fun p' hp' => hns p' (List.mem_cons_of_mem _ hp'))
    refine ⟨ls ++ ls', t2, m2, PRun.append r1 r2, hq2, fun l hl e he => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨h1, h2⟩ := hev l hl e he
      exact ⟨h1, hK p List.mem_cons_self code ls1 hc hcl _ h2⟩
    · exact hev2 l hl e he

/-- **At a `Q` state the first line of the remaining items' code is at the pc** (a plain
instruction line). -/
theorem q_head {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩)) {x : Insn} {t : Option Clif.TrapCode}
    (hpl : (Line.ins x t).plain = true)
    (hh : ∀ vb code, R.vc.blocks[b]? = some vb → itemsCode R.fr vb its = .ok code →
      ∀ ps ls ps', codeLinesE R.ctx R.af code ps = .ok (ls, ps') → ls.head? = some (.ins x t)) :
    ∃ j, R.fa.lines.toList[j]? = some (.ins x t) ∧ Arm.r .PC s = R.pcOf j ∧ StRel R s m w := by
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T, hvb, -, -, -, hcode, hls, -, hdrop, hpc, hst⟩ :=
    hq
  have hhd := hh vb code hvb hcode ps1 ls ps2 hls
  obtain ⟨rest, rfl⟩ : ∃ rest, ls = .ins x t :: rest := by
    cases ls with
    | nil => simp at hhd
    | cons ln rest => simp at hhd; exact ⟨rest, by rw [hhd]⟩
  have hZ : ∀ n, (rest ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ hls _ (List.mem_cons_of_mem _ hm) n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hd : R.L.drop j = .ins x t :: (relaxLines R.far (ftList (rest ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, show (Line.ins x t :: rest) ++ nxtOf R.af b = [.ins x t] ++ (rest ++ nxtOf R.af b)
      by simp, ftR_plain_append _ _ _ (by simpa using hpl) hZ]
    simp
  refine ⟨j, ?_, hpc, hst⟩
  have := congrArg (·[0]?) hd
  simp only [List.getElem?_drop, RL.L, Nat.add_zero] at this
  rw [this]
  rfl

/-- The lines of code starting with `fence` start with `dmb ish`. -/
theorem codeLinesE_head_fence {ctx : FnCtx} {af : AFunc} {rest : List AInst} {ps ps' : Backend.PState}
    {ls : List Line} (h : codeLinesE ctx af (.inst .fence :: rest) ps = .ok (ls, ps')) :
    ls.head? = some (.ins .dmbish none) := by
  simp only [codeLinesE, ainstLines, lines_fence, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

/-- The store after a list of moves. -/
def movesM : List (Loc × Loc) → (Loc → CV) → Loc → CV
  | [], m => m
  | p :: mvs, m => movesM mvs (upd m p.2 (m p.1))

/-- **`moves_fwd` with `AInv`**: through a list of moves at the head of the items (no callee
restore among them), `AInv` is kept (`aInv_step`, a move step); the store after them is
`movesM`. -/
theorem moves_fwdA {R : RL} (hR : R.Wf) (P : AKind → Prop) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV) (mon : Mon),
      Q R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      AInv R (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      (∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → ∀ K ∈ kinds ls1, P K) →
      (∀ p ∈ mvs, p.1.isSave = false) →
      ∃ (ls : List Lab) (t' : ArmState × Mon),
        PRun Policy.arm R.step (OkPriv R) (s, mon) ls t' ∧
        Q R t'.1 (.run ⟨b, its, movesM mvs m, w⟩) ∧
        AInv R (.run ⟨b, its, movesM mvs m, w⟩) ∧ ∀ l ∈ ls, ∀ e ∈ l.evs, R.F e.addr ∧ P e.k
  | [], its, s, m, mon, hq, hA, _, _ =>
    ⟨[], (s, mon), .nil, hq, hA, fun _ h => absurd h List.not_mem_nil⟩
  | p :: mvs, its, s, m, mon, hq, hA, hK, hns => by
    obtain ⟨ls, t1, r1, hq1, code, ls1, hc, hcl, hev⟩ := move_fwd hR hq mon (hns p List.mem_cons_self)
    have hA1 := Backend.Proof.aInv_step hR hq hA (.move (src := p.1) (dst := p.2))
    obtain ⟨ls', t2, r2, hq2, hA2, hev2⟩ := moves_fwdA hR P mvs its t1.1 _ t1.2 hq1 hA1
      (fun p' hp' => hK p' (List.mem_cons_of_mem _ hp')) (fun p' hp' => hns p' (List.mem_cons_of_mem _ hp'))
    refine ⟨ls ++ ls', t2, PRun.append r1 r2, hq2, hA2, fun l hl e he => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨h1, h2⟩ := hev l hl e he
      exact ⟨h1, hK p List.mem_cons_self code ls1 hc hcl _ h2⟩
    · exact hev2 l hl e he

/-- **One precise step at an `ldar`/`stlr` line** (64 bits, registers `x p`, address `x q`),
reading the thread's own memory: a single event of kind `acqR` (`lb = 1`) or `relW`
(`lb = 0`), 8 bytes at the address register's value. -/
theorem excl_step_fwd {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t))
    (hh : x.hooked = false) (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.pcOf j) (herr : Arm.r .ERR s = .None) {lb p q : Nat}
    (hlb : lb = 0 ∨ lb = 1) (hp : p ≤ 30) (hq : q ≤ 30)
    (hx : ∀ env, x.armFields env = Insn.armFields.exclFields 64 1 lb 31 (.x p) (.x q))
    (mon : Mon) :
    ∃ (t1 : ArmState × Mon) (e : Ev), PRun Policy.arm R.step (OkPriv R) (s, mon) [⟨[e], false⟩] t1 ∧
      t1.1 = R.step s ∧ e.k = (if lb = 1 then .acqR else .relW) ∧ e.n = 8 ∧
      e.addr = read_gpr 64 (BitVec.ofNat 5 q) s := by
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh
    hprog hpc herr
  obtain ⟨sz, rn', rt', rfl, hrn, -, hsz⟩ := toArmInst_excl (hx _) ha
  simp only [Reg.encSP, hq, ite_true, pure, Except.pure, Except.ok.injEq] at hrn
  subst hrn
  have hsz' : sz = 3#2 := by rcases hsz with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | omega | exact h
  subst hsz'
  have hns : NoStx s := fun rel rs rn h => by
    rw [cls_of_decode hdec] at h
    simp [clsOf, exclCls] at h
    split at h <;> cases h
  obtain ⟨t1, r1, ht1⟩ := step_fwd hR hj hh hprog hpc herr hns mon
  have hq31 : BitVec.ofNat 5 q ≠ 31#5 := ofNat5_ne31 (by omega)
  rw [hev] at r1
  rcases hlb with rfl | rfl
  · simp only [instEvs, exclEvs, hq31, false_and, ite_false, exclKind,
      show BitVec.ofNat 1 0 = 0#1 from rfl, show ¬ (0#1 : BitVec 1) = 1#1 by decide,
      show BitVec.ofNat 1 1 = 1#1 from rfl, ite_true] at r1
    exact ⟨t1, _, r1, ht1, rfl, rfl, rfl⟩
  · simp only [instEvs, exclEvs, hq31, false_and, ite_false, exclKind,
      show BitVec.ofNat 1 1 = 1#1 from rfl, ite_true] at r1
    exact ⟨t1, _, r1, ht1, rfl, rfl, rfl⟩

theorem lines_loadAcquire (c : FnCtx) (ps : Backend.PState) {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} :
    (MInst.loadAcquire ty rt rn fl).lines c ps = .ok ([.ins (.ldar ty.bits rt rn) fl.trapCode], ps) :=
  rfl

theorem lines_storeRelease (c : FnCtx) (ps : Backend.PState) {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} :
    (MInst.storeRelease ty rt rn fl).lines c ps = .ok ([.ins (.stlr ty.bits rt rn) fl.trapCode], ps) :=
  rfl

/-- The lines of code starting with `loadAcquire` start with its `ldar`. -/
theorem codeLinesE_head_ldar {ctx : FnCtx} {af : AFunc} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} {rest : List AInst} {ps ps' : Backend.PState} {ls : List Line}
    (h : codeLinesE ctx af (.inst (.loadAcquire ty rt rn fl) :: rest) ps = .ok (ls, ps')) :
    ls.head? = some (.ins (.ldar ty.bits rt rn) fl.trapCode) := by
  simp only [codeLinesE, ainstLines, lines_loadAcquire, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

/-- The lines of code starting with `storeRelease` start with its `stlr`. -/
theorem codeLinesE_head_stlr {ctx : FnCtx} {af : AFunc} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} {rest : List AInst} {ps ps' : Backend.PState} {ls : List Line}
    (h : codeLinesE ctx af (.inst (.storeRelease ty rt rn fl) :: rest) ps = .ok (ls, ps')) :
    ls.head? = some (.ins (.stlr ty.bits rt rn) fl.trapCode) := by
  simp only [codeLinesE, ainstLines, lines_storeRelease, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

end Concurrency.ArmAllocThread
