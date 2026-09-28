import FV.Opt.Proof.SimpFacts
import FV.Opt.Proof.GvnEdit

/-!
# The simplify validator is sound: `simpOk` and the run's facts ⇒ `g` simulates `f`

`Opt.simpOk_sim`: if `simpOk f g fi cert` holds and the certificate's semantic facts
(`Opt.SimpFacts`, proven for every run of the pass in `FV/Opt/Proof/SimpLoop.lean`) hold, then
`FunSim f g`. The structure mirrors `Opt.editOk_sim` (`FV/Opt/Proof/GvnEdit.lean`): source and
target frames are related at corresponding positions of the same block (`Opt.SRel`): both
satisfy the run-time invariant `Opt.Inv`, every value available in the source has its renaming
`σ v` available in the target with the same value, and the target position is where the
record of the source's next statement starts.

Each source step is matched by the target executing that statement's record: inserted pure
nodes (target-only steps that cannot fail, lemma (T)), then the statement's own output. The
semantic facts are used through the *graph valuation* of the target frame: every value available
in the target is the `den` of the certificate graph (`den_agree`: available values are leaves
or pure definitions whose node is the certificate's), evaluated from the leaf valuation
`rhoAt` read off the target registers; so a fact "`w` has the value of `n`" becomes a fact
about the target's registers.

A branch that the rules redirect to a trap block (`BrRefines`) becomes a trap in the target at
once: the source still runs the trap block's pure body, related to the stopped target by
`Frozen`.
-/

namespace Opt

open Clif

/-! ## Link-time symbols -/

/-- Replace the symbols of an instruction result's memory. -/
def resSyms (S : String → Option Nat) : Res (List Val × Mem) → Res (List Val × Mem)
  | .ok (vs, m) => .ok (vs, { m with symbols := S })
  | .trap c => .trap c
  | .stuck msg => .stuck msg

theorem resSyms_bind {α : Type} (S : String → Option Nat) (r : Res α)
    (k : α → Res (List Val × Mem)) : resSyms S (r >>= k) = r >>= fun a => resSyms S (k a) := by
  cases r <;> rfl

theorem resSyms_pure (S : String → Option Nat) (vs : List Val) (m : Mem) :
    resSyms S (pure (vs, m)) = pure (vs, { m with symbols := S }) := rfl

theorem resSyms_trap (S : String → Option Nat) (c : TrapCode) :
    resSyms S (.trap c) = .trap c := rfl

theorem Mem.load_syms (m : Mem) (S : String → Option Nat) (fl : MemFlags) (a n w : Nat) :
    Mem.load { m with symbols := S } fl a n w = Mem.load m fl a n w := rfl

theorem Mem.store_syms {w : Nat} (m : Mem) (S : String → Option Nat) (fl : MemFlags) (a n : Nat)
    (x : BitVec w) :
    Mem.store { m with symbols := S } fl a n x =
      (Mem.store m fl a n x >>= fun m' => pure { m' with symbols := S }) := by
  have h1 : Mem.checkAccess { m with symbols := S } fl a n = m.checkAccess fl a n := rfl
  have h2 : Mem.readonlyAt { m with symbols := S } a n = m.readonlyAt a n := rfl
  have h3 : Mem.writeBits { m with symbols := S } (fl.endianness == some .big) a n x =
      { m.writeBits (fl.endianness == some .big) a n x with symbols := S } := rfl
  simp only [Mem.store, h1, h2, h3]
  cases Mem.checkAccess m fl a n <;> try rfl
  simp only [Res.ok_bind]
  cases Res.check (!m.readonlyAt a n) _ <;> rfl

/-- Only `symbol_value` reads the symbols; nothing changes them. -/
theorem evalInst_withSyms {fr : Frame} {m : Mem} {i : Inst} (hi : notSym i = true)
    (S : String → Option Nat) :
    evalInst fr { m with symbols := S } i = resSyms S (evalInst fr m i) := by
  cases i <;> simp only [notSym] at hi <;> (try cases hi) <;>
    simp only [evalInst, resSyms_bind, resSyms_pure, resSyms_trap, apply_ite (resSyms S),
      Mem.load_syms, Mem.store_syms, bind_assoc, pure_bind]
  all_goals try rfl
  rename_i op _ _
  cases op <;> rfl

/-- `mem'` defines every symbol `mem` defines. -/
def SymsLe (mem mem' : Mem) : Prop := ∀ s a, mem.symbols s = some a → mem'.symbols s = some a

theorem evalNode_symsLe {fr : Frame} {m m' : Mem} {n : Inst} (hp : isPure n = true)
    (hle : SymsLe m m') {a : Val} (h : evalNode fr m n = some a) : evalNode fr m' n = some a := by
  cases hs : notSym n with
  | true =>
    rw [evalNode_mem (m := { m with symbols := m'.symbols }) (m' := m') hp rfl, evalNode_eq_val1,
      evalInst_withSyms hs]
    rw [evalNode_eq_val1] at h
    revert h
    cases evalInst fr m n with
    | ok p =>
      obtain ⟨vs, _⟩ := p
      rcases vs with _ | ⟨v, _ | _⟩ <;> simp [resSyms, val1]
    | trap c => simp [resSyms, val1]
    | stuck _ => simp [resSyms, val1]
  | false =>
    cases n <;> simp only [notSym] at hs <;> (try cases hs)
    rename_i ty gv
    simp only [evalNode, evalInst, Res.bind_eq_ok] at h ⊢
    revert h
    cases fr.func.globals.lookup gv with
    | none => simp [Res.ofOption, bind, Res.bind]
    | some g =>
      cases g with
      | symbol name off col =>
        cases hn : m.symbols name with
        | none => simp [Res.ofOption, bind, Res.bind, hn]
        | some b => simp [Res.ofOption, bind, Res.bind, hn, hle name b hn]
      | _ => simp [Res.ofOption, bind, Res.bind]

/-! ## The graph valuation -/

theorem den_mono_leaves {D : ValueId → Option Inst} {ρ ρ' : Valuation} {fr : Frame} {mem : Mem}
    (h : Valuation.Le ρ ρ') : Valuation.Le (den D ρ fr mem) (den D ρ' fr mem) :=
  den_le_of (fun x n a hx he => by rw [den_node hx]; exact he)
    (fun x a hx hρ => by rw [den_leaf hx]; exact h x a hρ)

theorem termEval_congr {fr fr' : Frame} {mem : Mem} {t : Terminator}
    (hr : ∀ x ∈ termOperands t, fr'.regs x = fr.regs x) : termEval fr' mem t = termEval fr mem t := by
  cases t <;> simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap] at hr <;>
    simp only [termEval]
  · rw [getMany_congr (fun x hx => hr x hx)]
  · rename_i c th el
    have hc : fr'.get c = fr.get c := by simp only [Frame.get, hr c (.inl (.inl rfl))]
    rw [hc]
    cases fr.get c with
    | ok cv =>
      simp only [Res.ok_bind]
      rw [getMany_congr (fun x hx => hr x (by split at hx <;> simp [hx]))]
    | _ => rfl
  · rename_i x d tbl
    have hc : fr'.get x = fr.get x := by simp only [Frame.get, hr x (.inl (.inl rfl))]
    rw [hc]
    cases fr.get x with
    | ok xv =>
      simp only [Res.ok_bind]
      refine congrArg (· >>= _) (getMany_congr (fun y hy => hr y ?_))
      cases hq : tbl[xv.toNat]? with
      | none => rw [hq] at hy; exact .inl (.inr hy)
      | some q => rw [hq] at hy; exact .inr ⟨q, List.mem_of_getElem? hq, hy⟩
    | _ => rfl

/-! ## Renamings -/

theorem mapOperands_congr {σ τ : ValueId → ValueId} {i : Inst}
    (h : ∀ x ∈ operands i, σ x = τ x) : mapOperands σ i = mapOperands τ i := by
  cases i <;> simp only [operands, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, false_imp_iff, imp_true_iff] at h <;> simp only [mapOperands, h]
  rename_i args
  simp only [Inst.call.injEq, true_and]
  exact List.map_congr_left h

theorem mapOperands_id (i : Inst) : mapOperands id i = i := by
  cases i <;> simp [mapOperands]

theorem mapOperands_comp (σ τ : ValueId → ValueId) (i : Inst) :
    mapOperands σ (mapOperands τ i) = mapOperands (σ ∘ τ) i := by
  cases i <;> simp [mapOperands]

theorem mapBlockCall_congr {σ τ : ValueId → ValueId} {bc : BlockCall}
    (h : ∀ x ∈ bc.args, σ x = τ x) : mapBlockCall σ bc = mapBlockCall τ bc := by
  simp only [mapBlockCall, List.map_congr_left h]

theorem mapTerm_congr {σ τ : ValueId → ValueId} {t : Terminator}
    (h : ∀ x ∈ termOperands t, σ x = τ x) : mapTerm σ t = mapTerm τ t := by
  cases t <;> simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap] at h <;>
    simp only [mapTerm]
  · rw [mapBlockCall_congr h]
  · rename_i c th el
    rw [h c (.inl (.inl rfl)), mapBlockCall_congr (fun x hx => h x (.inl (.inr hx))),
      mapBlockCall_congr (fun x hx => h x (.inr hx))]
  · rename_i x d tbl
    rw [h x (.inl (.inl rfl)), mapBlockCall_congr (fun y hy => h y (.inl (.inr hy))),
      List.map_congr_left (fun bc hbc => mapBlockCall_congr (fun y hy => h y (.inr ⟨bc, hbc, hy⟩)))]
  · rw [List.map_congr_left h]
  · rw [List.map_congr_left h]

theorem mapTerm_id (t : Terminator) : mapTerm id t = t := by
  have : mapBlockCall id = id := by funext bc; simp [mapBlockCall]
  cases t <;> simp [mapTerm, this]

theorem mapTerm_comp (σ τ : ValueId → ValueId) (t : Terminator) :
    mapTerm σ (mapTerm τ t) = mapTerm (σ ∘ τ) t := by
  cases t <;> simp [mapTerm, mapBlockCall, Function.comp_def]

section Subst

variable {s : Subst}

theorem step_of_get {x w : ValueId} (h : s.get? x = some w) : s.step x = w := by
  simp only [Subst.step, h, Option.getD_some]

theorem step_of_not_contains {x : ValueId} (h : s.contains x = false) : s.step x = x := by
  simp only [Subst.step]
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h]; rfl

theorem chainFree_get (hc : s.chainFree = true) {x w : ValueId} (h : s.get? x = some w) :
    s.contains w = false := by
  simp only [Subst.chainFree, List.all_eq_true] at hc
  have := hc (x, w) (by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]; simpa [Std.HashMap.get?_eq_getElem?] using h)
  simpa using this

theorem step_fixed (hc : s.chainFree = true) (x : ValueId) : s.contains (s.step x) = false := by
  cases h : s.get? x with
  | some w => rw [step_of_get h]; exact chainFree_get hc h
  | none =>
    have : s.step x = x := by simp only [Subst.step, h, Option.getD_none]
    rw [this]
    cases hx : s.contains x with
    | false => rfl
    | true =>
      rw [hm_contains_iff] at hx; rw [h] at hx; cases hx

theorem step_idem (hc : s.chainFree = true) (x : ValueId) : s.step (s.step x) = s.step x :=
  step_of_not_contains (step_fixed hc x)

theorem mapOperands_step_idem (hc : s.chainFree = true) (i : Inst) :
    mapOperands s.step (mapOperands s.step i) = mapOperands s.step i := by
  rw [mapOperands_comp]
  exact mapOperands_congr (fun x _ => step_idem hc x)

theorem mapTerm_step_idem (hc : s.chainFree = true) (t : Terminator) :
    mapTerm s.step (mapTerm s.step t) = mapTerm s.step t := by
  rw [mapTerm_comp]
  exact mapTerm_congr (fun x _ => step_idem hc x)

theorem fixed_ops {i : Inst} (h : (operands i).all (fun x => !s.contains x) = true) :
    mapOperands s.step i = i := by
  conv => rhs; rw [← mapOperands_id i]
  refine mapOperands_congr (fun x hx => ?_)
  simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact step_of_not_contains (h x hx)

end Subst

/-! ## The facts of `simpOk` -/

/-- The certificate's typing and `f`'s dominator tree: the data `wfCert g` is checked with. -/
def gInfo (fi : Info) (cert : SimpCert) : Info := { fi with types := cert.types }

/-- The check context of block `i`. -/
def sctx (g : Function) (fi : Info) (cert : SimpCert) (i : Nat) : SimpCtx :=
  { subst := cert.subst,
    avail := fun k w => availB (defMap g).get? (ancB fi.cfg.idom fi.cfg.idom.size) i k w }

/-- The statements a list of records emits. -/
def outs (l : List StmtLog) : List Stmt := l.flatMap (·.out.toList)

/-- The facts of `simpOk`. -/
structure SOk (f g : Function) (fi : Info) (cert : SimpCert) : Prop where
  wff : Wf f (wfData f fi)
  wfg : Wf g (wfData g (gInfo fi cert))
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  globals : g.globals = f.globals
  externs : g.externs = f.externs
  len : g.blocks.length = f.blocks.length
  chain : cert.subst.chainFree = true
  blocks : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∃ (b' : Block) (lg : BlockLog),
    g.blocks[i]? = some b' ∧ cert.logs[i]? = some (some lg) ∧ b'.id = b.id ∧
    b'.params = b.params ∧ b'.body = (outs lg.stmts ++ lg.extra.toList).map (renStmt cert.subst.step) ∧
    b'.term = mapTerm cert.subst.step lg.term' ∧ lg.term = mapTerm cert.subst.step b.term ∧
    (sctx g fi cert i).termOk lg = true ∧ (sctx g fi cert i).stmtsOk b.body lg.stmts 0 = true ∧
    (∀ p ∈ b.params, cert.defs.contains p.1 = false ∧ (initAvail f).contains p.1 = true ∧
      cert.subst.contains p.1 = false) ∧
    (∀ t ∈ b'.body, ∀ x, t.results = [x] → isPure t.inst = true → cert.defs.get? x = some t.inst) ∧
    (∀ t ∈ b'.body, skeletonStmt t = true → ∀ r ∈ t.results,
      cert.defs.contains r = false ∧ (initAvail f).contains r = true)

theorem simpOk_facts {f g : Function} {fi : Info} {cert : SimpCert}
    (hf : check f = .ok fi) (h : simpOk f g fi cert = true) : SOk f g fi cert := by
  simp only [simpOk, sameHeader, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hs⟩, hsl⟩, hgl⟩, hex⟩, hlen⟩, hch⟩, hwf⟩, hbl⟩ := h
  refine ⟨wf_of_check hf, wfCert_sound (info := gInfo fi cert) hwf, hn, hs, hsl, hgl, hex, hlen,
    hch, ?_⟩
  intro i b hb
  have hi : i < g.blocks.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hb).1
  have hz : ((b, g.blocks[i]), i) ∈ (f.blocks.zip g.blocks).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_zip_eq_some, hb, hi]
  have := hbl _ hz
  simp only at this
  split at this
  · rename_i lg hlg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩, h11⟩ := this
    refine ⟨g.blocks[i], lg, by simp [hi], hlg, h1, h2, ?_, h4, h5, h6, h7, ?_, ?_, ?_⟩
    · rw [h3]; simp [outs]
    · intro p hp
      have := h8 p hp
      exact ⟨this.1.1, this.1.2, this.2⟩
    · intro t ht x hx hp
      have := h10 t ht
      rw [hx] at this
      simpa [hp] using this
    · intro t ht hsk r hr
      rcases h11 t ht with h | h
      · rw [hsk] at h; cases h
      · exact h r hr
  · simp at this

/-! ## Target values are graph values -/

/-- Lexicographic induction on (rank of the block, position). -/
theorem lexInd {rank : Nat → Nat} {P : Nat → Nat → Prop}
    (h : ∀ d t, (∀ d' t', rank d' < rank d → P d' t') → (∀ t', t' < t → P d t') → P d t) :
    ∀ d t, P d t := by
  intro d
  induction hr : rank d using Nat.strongRecOn generalizing d with
  | _ n ih =>
    intro t
    induction t using Nat.strongRecOn with
    | _ t iht => exact h d t (fun d' t' hlt => ih (rank d') (hr ▸ hlt) d' rfl t') iht

/-- A value of the type `check f` gives `x` (the defaults of `rhoAt`). -/
def dflt (fi : Info) (x : ValueId) : Val :=
  match fi.types.get? x with
  | some t => ⟨t, 0⟩
  | none => ⟨.i8, 0⟩

open Classical in
/-- The leaf valuation read off the target frame `fr'` at `(bi, k')`: available leaves have their
register values, the other leaves typed defaults. -/
noncomputable def rhoAt (f g : Function) (fi : Info) (cert : SimpCert) (fr' : Frame) (bi k' : Nat) :
    Valuation := fun x =>
  if (initAvail f).contains x then
    some ((if Avail (wfData g (gInfo fi cert)) bi k' x then fr'.regs x else none).getD (dflt fi x))
  else none

/-- The memory with every symbol defined (undefined ones at address 0). -/
def memPlus (m : Mem) : Mem :=
  { m with symbols := fun n => match m.symbols n with
    | some a => some a
    | none => some 0 }

theorem memPlus_le (m : Mem) : SymsLe m (memPlus m) := by
  intro s a h; simp [memPlus, h]

theorem memPlus_all (m : Mem) (n : String) : ((memPlus m).symbols n).isSome := by
  simp only [memPlus]; split <;> simp_all

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
include hS

/-- The facts of `simpOk` for block `d` of `g`. -/
theorem SOk.gblock {d : Nat} {b' : Block} (hb' : g.blocks[d]? = some b') :
    ∃ b lg, f.blocks[d]? = some b ∧ cert.logs[d]? = some (some lg) ∧ b'.id = b.id ∧
    b'.params = b.params ∧ b'.body = (outs lg.stmts ++ lg.extra.toList).map (renStmt cert.subst.step) ∧
    b'.term = mapTerm cert.subst.step lg.term' ∧ lg.term = mapTerm cert.subst.step b.term ∧
    (sctx g fi cert d).termOk lg = true ∧ (sctx g fi cert d).stmtsOk b.body lg.stmts 0 = true ∧
    (∀ p ∈ b.params, cert.defs.contains p.1 = false ∧ (initAvail f).contains p.1 = true ∧
      cert.subst.contains p.1 = false) ∧
    (∀ t ∈ b'.body, ∀ x, t.results = [x] → isPure t.inst = true → cert.defs.get? x = some t.inst) ∧
    (∀ t ∈ b'.body, skeletonStmt t = true → ∀ r ∈ t.results,
      cert.defs.contains r = false ∧ (initAvail f).contains r = true) := by
  have hd : d < f.blocks.length := by rw [← hS.len]; exact (List.getElem?_eq_some_iff.1 hb').1
  obtain ⟨b'', lg, hb'', h⟩ := hS.blocks d f.blocks[d] (by simp [hd])
  rw [hb'] at hb''; cases hb''
  exact ⟨f.blocks[d], lg, by simp [hd], h⟩

/-- A defined value of `g` is a leaf (a parameter or a result of a non-pure-node statement,
not a graph node) or a pure statement whose node is the graph's. -/
theorem SOk.site {x : ValueId} {d t : Nat} (hd : (wfData g (gInfo fi cert)).dm x = some (d, t)) :
    (cert.graph x = none ∧ (initAvail f).contains x = true) ∨
    (∃ n, cert.graph x = some n ∧ PureDef g (wfData g (gInfo fi cert)) x n) := by
  cases t with
  | zero =>
    obtain ⟨b', p, hb', hp, hpx⟩ := site_param' hS.wfg hd
    obtain ⟨b, lg, hb, -, -, hpar, -, -, -, -, -, hps, -⟩ := hS.gblock hb'
    rw [hpar] at hp
    obtain ⟨h1, h2, -⟩ := hps p hp
    subst hpx
    refine .inl ⟨?_, h2⟩
    simp only [SimpCert.graph]
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h1]
  | succ j =>
    obtain ⟨b', st, hb', hst, hx⟩ := site_stmt hS.wfg hd
    obtain ⟨b, lg, hb, -, -, -, -, -, -, -, -, -, hpure, hskel⟩ := hS.gblock hb'
    have hmem : st ∈ b'.body := List.mem_of_getElem? hst
    cases hsk : skeletonStmt st with
    | true =>
      obtain ⟨h1, h2⟩ := hskel st hmem hsk x hx
      refine .inl ⟨?_, h2⟩
      simp only [SimpCert.graph]
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h1]
    | false =>
      simp only [skeletonStmt, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hsk
      obtain ⟨hp, hl⟩ := hsk
      have hr : st.results = [x] := by
        match hrs : st.results, hl with
        | [y], _ => rw [hrs] at hx; simp at hx; rw [hx]
      exact .inr ⟨st.inst, hpure st hmem x hr hp, d, j, b', st, hd, hb', hst, hr, rfl, hp⟩

/-- **Target values are graph values**: at any point of a run of `g`, every available value is
the `den` of the certificate graph from the leaves `rhoAt` (in any memory defining the
symbols). -/
theorem den_agree {syms : String → Option Nat} {fr' : Frame} {bi k' : Nat}
    (hinv : Inv g (wfData g (gInfo fi cert)) syms fr' bi k') {mem : Mem}
    (hmem : SymsLe (symMem syms) mem) :
    ∀ x, Avail (wfData g (gInfo fi cert)) bi k' x →
      den cert.graph (rhoAt f g fi cert fr' bi k') fr' mem x = fr'.regs x := by
  have key : ∀ d t x, (wfData g (gInfo fi cert)).dm x = some (d, t) →
      Avail (wfData g (gInfo fi cert)) bi k' x →
      den cert.graph (rhoAt f g fi cert fr' bi k') fr' mem x = fr'.regs x := by
    refine lexInd (rank := (wfData g (gInfo fi cert)).rank) ?_
    intro d t ihr iht x hd hx
    obtain ⟨a, ha, -⟩ := hinv.regs x hx
    rcases hS.site hd with ⟨hn, hL⟩ | ⟨n, hn, hpd⟩
    · rw [den_leaf hn, ha]
      simp [rhoAt, hL, hx, ha]
    · rw [den_node hn, ha]
      obtain ⟨d0, j, b', st, hd0, hb', hst, hrx, hsn, hp⟩ := hpd
      rw [hd] at hd0
      simp only [Option.some.injEq, Prod.mk.injEq] at hd0
      obtain ⟨rfl, rfl⟩ := hd0
      have hev : evalNode fr' (symMem syms) n = some a := (hinv.pure x n hx ⟨d, j, b', st, hd, hb',
        hst, hrx, hsn, hp⟩).symm.trans ha
      refine (evalNode_congr (fr := fr')
        (fr' := withRegs fr' (den cert.graph (rhoAt f g fi cert fr' bi k') fr' mem)) rfl rfl ?_).trans
        (evalNode_symsLe hp hmem hev)
      intro y hy
      rw [← hsn] at hy
      have hyd := hS.wfg.uses d b' hb' j st hst y hy
      have hyk := avail_operand hS.wfg hx hd hb' hst hy
      obtain ⟨d2, t2, hd2, hya⟩ := hyd
      rcases hya with ⟨rfl, ht2⟩ | ⟨hne, hanc⟩
      · exact iht t2 (by omega) y hd2 hyk
      · exact ihr d2 t2 ((hanc.rank_le hS.wfg.rank).2 hne) y hd2 hyk
  intro x hx
  obtain ⟨d, t, hd, -⟩ := id hx
  exact key d t x hd hx

end

/-- The graph valuation of the target frame `fr'` at `(bi, k')` (in memory `memPlus m`). -/
noncomputable def VAt (f g : Function) (fi : Info) (cert : SimpCert) (fr' : Frame) (bi k' : Nat)
    (m : Mem) : Valuation :=
  den cert.graph (rhoAt f g fi cert fr' bi k') fr' (memPlus m)

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
include hS

theorem rhoAt_good (hF : SimpFacts f fi cert) {syms : String → Option Nat} {fr' : Frame}
    {bi k' : Nat} (hinv : Inv g (wfData g (gInfo fi cert)) syms fr' bi k') (m : Mem) :
    SGood f fi (rhoAt f g fi cert fr' bi k') fr' (memPlus m) where
  env := ⟨by rw [hinv.func, hS.globals], fun s hs => hinv.slots s (by rw [hS.slots]; exact hs),
    memPlus_all m⟩
  dom := by
    intro x
    simp only [rhoAt]
    split <;> simp_all
  ty := by
    intro x a t hx ht
    simp only [rhoAt] at hx
    split at hx
    · simp only [Option.some.injEq] at hx
      subst hx
      split
      · rename_i hav
        obtain ⟨b, hb, htb⟩ := hinv.regs x hav
        rw [hb]
        have h2 := hF.types x t ht
        simp only [wfData, gInfo] at htb
        rw [htb] at h2
        exact (Option.some.inj h2)
      · simp only [dflt, ht, Option.getD_none]
    · cases hx

/-- The facts of the run, read in the target frame. -/
theorem facts_at (hF : SimpFacts f fi cert) {syms : String → Option Nat} {fr' : Frame}
    {bi k' : Nat} (hinv : Inv g (wfData g (gInfo fi cert)) syms fr' bi k') {m : Mem}
    (hm : m.symbols = syms) {i : Nat} {lg : BlockLog} (hlg : cert.logs[i]? = some (some lg)) :
    BlockFact (fun b => (trapMap f).get? b) (withRegs fr' (VAt f g fi cert fr' bi k' m))
      (memPlus m) (VAt f g fi cert fr' bi k' m) lg ∧
    ∀ x, Avail (wfData g (gInfo fi cert)) bi k' x → VAt f g fi cert fr' bi k' m x = fr'.regs x :=
  ⟨hF.facts _ _ _ (rhoAt_good hS hF hinv m) i lg hlg,
   den_agree hS hinv (by intro s a h; exact memPlus_le m s a (by rw [hm]; exact h))⟩

end

/-! ## Records -/

theorem stmtsOk_spec {c : SimpCtx} : ∀ {ss : List Stmt} {lgs : List StmtLog} {k0 : Nat},
    c.stmtsOk ss lgs k0 = true → ss.length = lgs.length ∧
      ∀ j s l, ss[j]? = some s → lgs[j]? = some l →
        c.stmtOk s (k0 + (outs (lgs.take j)).length) l = true
  | [], [], _, _ => ⟨rfl, fun j s l h _ => by simp at h⟩
  | [], _ :: _, _, h => by simp [SimpCtx.stmtsOk] at h
  | _ :: _, [], _, h => by simp [SimpCtx.stmtsOk] at h
  | s :: ss, l :: lgs, k0, h => by
    simp only [SimpCtx.stmtsOk, Bool.and_eq_true] at h
    obtain ⟨hl, hj⟩ := stmtsOk_spec h.2
    refine ⟨by simp [hl], fun j s' l' hs hl' => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hl'
      subst hs hl'
      simpa [outs] using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hs hl'
      have := hj j s' l' hs hl'
      simp only [List.take_succ_cons, outs, List.flatMap_cons, List.length_append] at this ⊢
      rw [Array.length_toList, ← Nat.add_assoc]
      exact this

theorem outs_take_succ {lgs : List StmtLog} {j : Nat} {l : StmtLog} (h : lgs[j]? = some l) :
    outs (lgs.take (j + 1)) = outs (lgs.take j) ++ l.out.toList := by
  simp [outs, List.take_add_one, h]

theorem outs_take_drop (lgs : List StmtLog) (j : Nat) :
    outs lgs = outs (lgs.take j) ++ outs (lgs.drop j) := by
  simp only [outs, ← List.flatMap_append, List.take_append_drop]

theorem outs_drop_cons {lgs : List StmtLog} {j : Nat} {l : StmtLog} (h : lgs[j]? = some l) :
    outs (lgs.drop j) = l.out.toList ++ outs (lgs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1]
  simp [outs, (List.getElem?_eq_some_iff.1 h).2]

theorem insOk_renStmt (σ : ValueId → ValueId) (t : Stmt) : insOk (renStmt σ t) = insOk t := by
  simp only [insOk, renStmt, isPure_mapOperands]
  cases t.inst <;> rfl

/-! ## The relation -/

/-- The definition of `σ v` in the target is in a dominator of the definition of `v`. -/
def SiteAnc (f g : Function) (fi : Info) (cert : SimpCert) (v : ValueId) : Prop :=
  ∀ d t, (wfData f fi).dm v = some (d, t) → ∃ d' t',
    (wfData g (gInfo fi cert)).dm (cert.subst.step v) = some (d', t') ∧ Anc fi.cfg.idom d' d

/-- Frames at positions `k` (source) and `k'` (target) of block `bi`, without the position
constraint. -/
structure SCore (f g : Function) (fi : Info) (cert : SimpCert) (syms : String → Option Nat)
    (fr fr' : Frame) (bi k k' : Nat) : Prop where
  invf : Inv f (wfData f fi) syms fr bi k
  invg : Inv g (wfData g (gInfo fi cert)) syms fr' bi k'
  agree : ∀ v, Avail (wfData f fi) bi k v →
    Avail (wfData g (gInfo fi cert)) bi k' (cert.subst.step v) ∧
      fr'.regs (cert.subst.step v) = fr.regs v ∧ SiteAnc f g fi cert v
  slots : fr'.slots = fr.slots

/-- Frames before source statement `k` and at the start of its record in the target. -/
structure SRel (f g : Function) (fi : Info) (cert : SimpCert) (syms : String → Option Nat)
    (fr fr' : Frame) (bi k k' : Nat) : Prop extends SCore f g fi cert syms fr fr' bi k k' where
  pos : ∀ lg, cert.logs[bi]? = some (some lg) → k' = (outs (lg.stmts.take k)).length

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- A target-only pure statement that evaluates. -/
theorem SCore.tpure {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {t : Stmt} {ts : List Stmt}
    {u : ValueId} {a : Val} (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms)
    (ht : fr'.body = t :: ts) (hp : isPure t.inst = true) (hu : t.results = [u])
    (hev : evalNode fr' m t.inst = some a) :
    lstep fr' m = .next { fr' with regs := fr'.regs.set u a, body := ts } m ∧
      SCore f g fi cert syms fr { fr' with regs := fr'.regs.set u a, body := ts } bi k (k' + 1) := by
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  rw [h2] at ht
  obtain ⟨htk, -, -⟩ := drop_eq_cons ht
  rw [← h2] at ht
  have hnc : ∀ fn args, t.inst ≠ .call fn args := by
    intro fn args he; rw [he] at hp; cases hp
  have he : evalInst fr' m t.inst = .ok ([a], m) := by
    simp only [evalNode] at hev
    split at hev
    · rename_i r m' he
      cases hev
      rw [he, (evalInst_pure hp he).1]
    · cases hev
  have hset : fr'.regs.setMany t.results [a] = some (fr'.regs.set u a) := by
    rw [hu]; rfl
  refine ⟨?_, ⟨h.invf, ?_, ?_, h.slots⟩⟩
  · rw [lstep_inst ht hnc]
    simp only [he, LRes.ofRes, hset]
  · refine Inv.results hS.wfg h.invg ht (fun ts0 h0 => evalInst_types he h0)
      (fun _ => ⟨a, rfl, ?_⟩) hset
    rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact hev
  · intro v hv
    obtain ⟨hav, heq, hsa⟩ := h.agree v hv
    have hnr := avail_not_result hS.wfg hb' htk hav
    rw [hu] at hnr
    refine ⟨hav.mono (by omega), ?_, hsa⟩
    simp only [List.mem_singleton] at hnr
    simp only [Regs.set_other _ _ hnr, heq]

/-- An inserted statement evaluates (lemma (T)). -/
theorem SCore.insEval {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {t : Stmt} {ts : List Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (ht : fr'.body = t :: ts) (hins : insOk t = true) :
    isPure t.inst = true ∧ ∃ u a, t.results = [u] ∧ evalNode fr' m t.inst = some a := by
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  rw [h2] at ht
  obtain ⟨htk, -, -⟩ := drop_eq_cons ht
  obtain ⟨hp, u, hu, hns⟩ := insOk_spec hins
  obtain ⟨a, ha⟩ := evalInst_total (f := g) (tm := (wfData g (gInfo fi cert)).tm) (fr := fr')
    (mem := m) hp (hS.wfg.pure bi b' hb' k' t htk hp) (by rw [h.invg.func])
    (fun x hx => h.invg.regs x (hS.wfg.uses bi b' hb' k' t htk x hx)) h.invg.slots
    (fun ty gv _ _ _ he => absurd he (hns ty gv))
  exact ⟨hp, u, a, hu, by simp [evalNode, ha]⟩

/-- The target executes inserted statements. -/
theorem SCore.insList {fr : Frame} {bi k : Nat} {m : Mem} (hm : m.symbols = syms) :
    ∀ (L : List Stmt) {fr' : Frame} {k' : Nat} {rest : List Stmt},
      SCore f g fi cert syms fr fr' bi k k' → fr'.body = L ++ rest → (∀ t ∈ L, insOk t = true) →
      ∃ fr'', LStar fr' m fr'' m ∧ SCore f g fi cert syms fr fr'' bi k (k' + L.length) ∧
        fr''.body = rest ∧ fr''.term = fr'.term ∧ fr''.func = fr'.func ∧ fr''.slots = fr'.slots
  | [], fr', k', rest, h, hb, _ => ⟨fr', .refl _ _, h, by simpa using hb, rfl, rfl, rfl⟩
  | t :: L, fr', k', rest, h, hb, hins => by
    have hb' : fr'.body = t :: (L ++ rest) := by rw [hb]; rfl
    obtain ⟨hp, u, a, hu, hev⟩ := h.insEval hS (m := m) hb' (hins t (by simp))
    obtain ⟨hl, h1⟩ := h.tpure hS hm hb' hp hu hev
    obtain ⟨fr'', hst, h2, hb2, ht2, hf2, hs2⟩ := SCore.insList hm L h1 rfl
      (fun t' ht' => hins t' (by simp [ht']))
    exact ⟨fr'', .step hl hst, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2, hb2, ht2, hf2, hs2⟩

end

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- Where the relation stands before a source statement. -/
theorem SRel.cur {fr fr' : Frame} {bi k k' : Nat} {s : Stmt} {ss : List Stmt}
    (h : SRel f g fi cert syms fr fr' bi k k') (hs : fr.body = s :: ss) :
    ∃ b b' lg l, f.blocks[bi]? = some b ∧ g.blocks[bi]? = some b' ∧
      cert.logs[bi]? = some (some lg) ∧ b.body[k]? = some s ∧ lg.stmts[k]? = some l ∧
      (sctx g fi cert bi).stmtOk s k' l = true ∧
      fr'.body = (l.out.toList ++ outs (lg.stmts.drop (k + 1)) ++ lg.extra.toList).map
        (renStmt cert.subst.step) ∧
      (outs (lg.stmts.take (k + 1))).length = k' + l.out.size := by
  obtain ⟨b, hb, h1, -, -⟩ := h.invf.block
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  obtain ⟨b'', lg, hb'', hlg, -, -, hbody, -, -, -, hok, -⟩ := hS.blocks bi b hb
  rw [hb'] at hb''; cases hb''
  rw [h1] at hs
  obtain ⟨hsk, -, hkl⟩ := drop_eq_cons hs
  obtain ⟨hlen, hspec⟩ := stmtsOk_spec hok
  have hkl' : k < lg.stmts.length := by rw [← hlen]; exact hkl
  have hl : lg.stmts[k]? = some lg.stmts[k] := by simp [hkl']
  have hpos := h.pos lg hlg
  refine ⟨b, b', lg, lg.stmts[k], hb, hb', hlg, hsk, hl, ?_, ?_, ?_⟩
  · have := hspec k s _ hsk hl
    rwa [Nat.zero_add, ← hpos] at this
  · rw [h2, hbody, ← List.map_drop, outs_take_drop lg.stmts k,
      List.append_assoc, hpos, List.drop_left, outs_drop_cons hl, List.append_assoc]
  · rw [outs_take_succ hl, List.length_append, ← hpos, Array.length_toList]

/-- Where the relation stands at the terminator. -/
theorem SRel.atEnd {fr fr' : Frame} {bi k k' : Nat} (h : SRel f g fi cert syms fr fr' bi k k')
    (hs : fr.body = []) :
    ∃ b b' lg, f.blocks[bi]? = some b ∧ g.blocks[bi]? = some b' ∧
      cert.logs[bi]? = some (some lg) ∧ fr.term = b.term ∧
      fr'.term = mapTerm cert.subst.step lg.term' ∧ lg.term = mapTerm cert.subst.step b.term ∧
      (sctx g fi cert bi).termOk lg = true ∧
      fr'.body = lg.extra.toList.map (renStmt cert.subst.step) ∧ k = b.body.length ∧
      b'.id = b.id ∧ b'.params = b.params := by
  obtain ⟨b, hb, h1, ht1, hk⟩ := h.invf.block
  obtain ⟨b', hb', h2, ht2, -⟩ := h.invg.block
  obtain ⟨b'', lg, hb'', hlg, hid, hpar, hbody, hterm, hlt, htok, hok, -⟩ := hS.blocks bi b hb
  rw [hb'] at hb''; cases hb''
  have hkk : k = b.body.length := by
    rw [hs] at h1
    have := List.drop_eq_nil_iff.1 h1.symm; omega
  obtain ⟨hlen, -⟩ := stmtsOk_spec hok
  have hpos := h.pos lg hlg
  rw [hkk, hlen, List.take_length] at hpos
  refine ⟨b, b', lg, hb, hb', hlg, ht1, by rw [ht2, hterm], hlt, htok, ?_, hkk, hid, hpar⟩
  rw [h2, hbody, ← List.map_drop, hpos, List.drop_left]

/-- The results of a statement bound in both frames at the same values keep the agreement. -/
theorem agree_bind {fr fr' : Frame} {bi k k' : Nat} {b : Block} {b' : Block} {s : Stmt}
    {rs : Inst} {vals : List Val} {regs regs' : Regs}
    (h : ∀ v, Avail (wfData f fi) bi k v →
      Avail (wfData g (gInfo fi cert)) bi k' (cert.subst.step v) ∧
        fr'.regs (cert.subst.step v) = fr.regs v ∧ SiteAnc f g fi cert v)
    (hb : f.blocks[bi]? = some b) (hb' : g.blocks[bi]? = some b') (hs : b.body[k]? = some s)
    (ht : b'.body[k']? = some { results := s.results, inst := rs })
    (hσ : ∀ r ∈ s.results, cert.subst.step r = r)
    (h1 : fr.regs.setMany s.results vals = some regs)
    (h2 : fr'.regs.setMany s.results vals = some regs') :
    ∀ v, Avail (wfData f fi) bi (k + 1) v →
      Avail (wfData g (gInfo fi cert)) bi (k' + 1) (cert.subst.step v) ∧
        regs' (cert.subst.step v) = regs v ∧ SiteAnc f g fi cert v := by
  intro v hv
  rcases avail_succ hS.wff hb hs hv with hr | hv'
  · rw [hσ v hr]
    have hg := site_result hS.wfg hb' ht hr
    refine ⟨⟨bi, k' + 1, hg, .inl ⟨rfl, Nat.le_refl _⟩⟩, (setMany_same h1 h2 v hr).symm, ?_⟩
    intro d t hd
    rw [site_result hS.wff hb hs hr] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    exact ⟨bi, k' + 1, by rw [hσ v hr]; exact hg, .refl _⟩
  · have hnr := avail_not_result hS.wff hb hs hv'
    obtain ⟨hav, heq, hsa⟩ := h v hv'
    have hnr' := avail_not_result hS.wfg hb' ht hav
    refine ⟨hav.mono (by omega), ?_, hsa⟩
    rw [((setMany_spec h2).2 _).1 hnr', ((setMany_spec h1).2 _).1 hnr, heq]

/-- A kept statement (not a call) steps in lock-step. -/
theorem SCore.lock {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss ts : List Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss)
    (ht : fr'.body = renStmt cert.subst.step s :: ts)
    (hσ : ∀ r ∈ s.results, cert.subst.step r = r) (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', lstep fr' m = .next fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + 1) ∧ fr1'.body = ts ∧ fr1.body = ss) ∧
    (∀ c, lstep fr m = .trap c → lstep fr' m = .trap c) := by
  obtain ⟨b, hb, h1, -, -⟩ := h.invf.block
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  have hs0 := hs; have ht0 := ht
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  have hops : ∀ x ∈ operands s.inst, fr'.regs (cert.subst.step x) = fr.regs x :=
    fun x hx => (h.agree x (hS.wff.uses bi b hb k s hsk x hx)).2.1
  have hglob : fr'.func.globals = fr.func.globals := by
    rw [h.invf.func, h.invg.func, hS.globals]
  have hev := evalInst_rename (mem := m) hglob h.slots hops
  have hnc' := mapOperands_not_call (σ := cert.subst.step) hnc
  rw [lstep_inst hs0 hnc, lstep_inst ht0 hnc']
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        have he' := Res.norm_eq_ok hev he
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [renStmt] at he' ⊢
        rw [he']
        simp only [LRes.ofRes, hset']
        refine ⟨_, rfl, ⟨?_, ?_, ?_, h.slots⟩, by first | rfl | trivial, by first | rfl | trivial⟩
        · exact Inv.results hS.wff h.invf hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · refine Inv.results hS.wfg h.invg ht0 (fun ts0 h0 => evalInst_types he' h0)
            (fun hp => ?_) hset'
          obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he'
          exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩
        · exact agree_bind hS h.agree hb hb' hsk (by rw [htk]; rfl) hσ hset hset'
      · cases hl
  · cases he : evalInst fr m s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' =>
      rw [he] at hl; cases hl
      simp only [renStmt]
      rw [Res.norm_eq_trap hev he]; rfl

/-- A source statement whose results the target already holds: the source steps alone. -/
theorem SCore.srcOnly {fr fr' : Frame} {bi k k' : Nat} {m m1 : Mem} {s : Stmt} {ss : List Stmt}
    {vals : List Val} {regs : Regs} (h : SCore f g fi cert syms fr fr' bi k k')
    (hm : m.symbols = syms) (hs : fr.body = s :: ss) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hev : evalInst fr m s.inst = .ok (vals, m1)) (hset : fr.regs.setMany s.results vals = some regs)
    (hres : ∀ r ∈ s.results, Avail (wfData g (gInfo fi cert)) bi k' (cert.subst.step r) ∧
      fr'.regs (cert.subst.step r) = regs r) :
    lstep fr m = .next { fr with regs, body := ss } m1 ∧
      SCore f g fi cert syms { fr with regs, body := ss } fr' bi (k + 1) k' := by
  obtain ⟨b, hb, h1, -, -⟩ := h.invf.block
  have hs0 := hs
  rw [h1] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  refine ⟨by rw [lstep_inst hs0 hnc]; simp only [hev, LRes.ofRes, hset], ⟨?_, h.invg, ?_, h.slots⟩⟩
  · exact Inv.results hS.wff h.invf hs0 (fun ts0 h0 => evalInst_types hev h0)
      (fun hp => by
        obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp hev
        exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩) hset
  · intro v hv
    rcases avail_succ hS.wff hb hsk hv with hr | hv'
    · obtain ⟨hav, heq⟩ := hres v hr
      refine ⟨hav, heq, ?_⟩
      intro d t hd
      rw [site_result hS.wff hb hsk hr] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      obtain ⟨d', t', hd', hva⟩ := hav
      refine ⟨d', t', hd', ?_⟩
      rcases hva with ⟨rfl, -⟩ | ⟨-, ha⟩
      · exact .refl _
      · exact ha
    · have hnr := avail_not_result hS.wff hb hsk hv'
      obtain ⟨hav, heq, hsa⟩ := h.agree v hv'
      refine ⟨hav, ?_, hsa⟩
      simp only
      rw [((setMany_spec hset).2 _).1 hnr, heq]

end

/-! ## Transport between the run and the graph valuation -/

theorem resSyms_eq_ok {S : String → Option Nat} {r : Res (List Val × Mem)} {vs : List Val}
    {m' : Mem} (h : resSyms S r = .ok (vs, m')) : ∃ m0, r = .ok (vs, m0) ∧ m' = { m0 with symbols := S } := by
  cases r with
  | ok p => obtain ⟨vs0, m0⟩ := p; simp only [resSyms, Res.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ⟨m0, rfl, rfl⟩
  | trap c => cases h
  | stuck _ => cases h

theorem resSyms_eq_trap {S : String → Option Nat} {r : Res (List Val × Mem)} {c : TrapCode}
    (h : resSyms S r = .trap c) : r = .trap c := by
  cases r with
  | ok p => obtain ⟨_, _⟩ := p; cases h
  | trap c' => exact h
  | stuck _ => cases h

theorem mem_syms_inj {a b : Mem} {S : String → Option Nat}
    (h : ({ a with symbols := S } : Mem) = { b with symbols := S }) (hs : a.symbols = b.symbols) :
    a = b := by
  cases a; cases b
  simp only [Mem.mk.injEq] at h hs ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, hs⟩

theorem memPlus_eq (m : Mem) : memPlus m = { m with symbols := (memPlus m).symbols } := rfl

/-- A (symbol-free) source instruction evaluated in the run and in the graph valuation. -/
theorem src_to_graph {fr F : Frame} {m : Mem} {i i' : Inst} (hi : notSym i = true)
    (hr : (evalInst F (memPlus m) i').norm = (evalInst fr (memPlus m) i).norm) :
    (∀ vals m1, evalInst fr m i = .ok (vals, m1) →
      evalInst F (memPlus m) i' = .ok (vals, { m1 with symbols := (memPlus m).symbols })) ∧
    (∀ c, evalInst fr m i = .trap c → evalInst F (memPlus m) i' = .trap c) := by
  have he : evalInst fr (memPlus m) i = resSyms (memPlus m).symbols (evalInst fr m i) := by
    rw [memPlus_eq m]; exact evalInst_withSyms hi _
  refine ⟨fun vals m1 h => ?_, fun c h => ?_⟩
  · exact Res.norm_eq_ok hr (by rw [he, h]; rfl)
  · exact Res.norm_eq_trap hr (by rw [he, h]; rfl)

/-- A (symbol-free) target instruction evaluated in the graph valuation and in the run. -/
theorem graph_to_tgt {fr' F : Frame} {m : Mem} {i : Inst} (hi : notSym i = true)
    (hr : evalInst F (memPlus m) i = evalInst fr' (memPlus m) i) :
    (∀ vals m1, m1.symbols = m.symbols →
      evalInst F (memPlus m) i = .ok (vals, { m1 with symbols := (memPlus m).symbols }) →
      evalInst fr' m i = .ok (vals, m1)) ∧
    (∀ c, evalInst F (memPlus m) i = .trap c → evalInst fr' m i = .trap c) := by
  have he : evalInst fr' (memPlus m) i = resSyms (memPlus m).symbols (evalInst fr' m i) := by
    rw [memPlus_eq m]; exact evalInst_withSyms hi _
  refine ⟨fun vals m1 hs h => ?_, fun c h => ?_⟩
  · rw [hr, he] at h
    obtain ⟨m0, h0, h1⟩ := resSyms_eq_ok h
    rw [h0, mem_syms_inj h1 (by rw [hs, evalInst_symbols h0])]
  · rw [hr, he] at h
    exact resSyms_eq_trap h

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- The source statement's renamed instruction, in the graph valuation of a later target point
`k''` whose values agree with the graph. -/
theorem SCore.srcRename {fr fr'' : Frame} {bi k k'' : Nat} {V : Valuation} {M : Mem} {b : Block}
    {s : Stmt} (h : SCore f g fi cert syms fr fr'' bi k k'') (hb : f.blocks[bi]? = some b)
    (hsk : b.body[k]? = some s)
    (hV : ∀ x, Avail (wfData g (gInfo fi cert)) bi k'' x → V x = fr''.regs x) :
    (evalInst (withRegs fr'' V) M (mapOperands cert.subst.step s.inst)).norm =
      (evalInst fr M s.inst).norm := by
  refine evalInst_rename (by simp only [withRegs]; rw [h.invf.func, h.invg.func, hS.globals])
    h.slots (fun x hx => ?_)
  obtain ⟨hav, heq, -⟩ := h.agree x (hS.wff.uses bi b hb k s hsk x hx)
  simp only [withRegs]
  rw [hV _ hav, heq]

/-- A target instruction at `k''` reads the same in the graph valuation and in the run. -/
theorem tgtGraph {fr'' : Frame} {bi k'' : Nat} {V : Valuation} {M : Mem} {b' : Block} {t : Stmt}
    (hb' : g.blocks[bi]? = some b') (htk : b'.body[k'']? = some t)
    (hV : ∀ x, Avail (wfData g (gInfo fi cert)) bi k'' x → V x = fr''.regs x) :
    evalInst (withRegs fr'' V) M t.inst = evalInst fr'' M t.inst :=
  evalInst_congr rfl rfl (fun x hx => hV x (hS.wfg.uses bi b' hb' k'' t htk x hx))

/-- A statement whose target counterpart `{ results := s.results, inst := i }` refines it. -/
theorem SCore.lockWith {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss ts : List Stmt}
    {i : Inst} (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms)
    (hs : fr.body = s :: ss) (ht : fr'.body = { results := s.results, inst := i } :: ts)
    (hσ : ∀ r ∈ s.results, cert.subst.step r = r) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hnc' : ∀ fn args, i ≠ .call fn args)
    (hok : ∀ vals m1, evalInst fr m s.inst = .ok (vals, m1) → evalInst fr' m i = .ok (vals, m1))
    (htr : ∀ c, evalInst fr m s.inst = .trap c → evalInst fr' m i = .trap c) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', lstep fr' m = .next fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + 1) ∧ fr1'.body = ts ∧ fr1.body = ss) ∧
    (∀ c, lstep fr m = .trap c → lstep fr' m = .trap c) := by
  obtain ⟨b, hb, h1, -, -⟩ := h.invf.block
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  have hs0 := hs; have ht0 := ht
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  rw [lstep_inst hs0 hnc, lstep_inst ht0 hnc']
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        have he' := hok _ _ he
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [he', LRes.ofRes, hset']
        refine ⟨_, rfl, ⟨?_, ?_, ?_, h.slots⟩, by first | rfl | trivial, by first | rfl | trivial⟩
        · exact Inv.results hS.wff h.invf hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · refine Inv.results hS.wfg h.invg ht0 (fun ts0 h0 => evalInst_types he' h0)
            (fun hp => ?_) hset'
          obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he'
          exact ⟨a, rfl, by rw [evalNode_mem (m := m) hp (by rw [hm]; rfl)]; exact ha⟩
        · exact agree_bind hS h.agree hb hb' hsk htk hσ hset hset'
      · cases hl
  · cases he : evalInst fr m s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' =>
      rw [he] at hl; cases hl
      rw [htr _ he]; rfl

end

/-! ## The statement records -/

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- The target runs the inserted statements `out` of a record; there the facts hold. -/
theorem SCore.runIns {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {out : Array Stmt}
    {R : List Stmt} {lg : BlockLog} (h : SCore f g fi cert syms fr fr' bi k k')
    (hm : m.symbols = syms) (hbody : fr'.body = out.toList.map (renStmt cert.subst.step) ++ R)
    (hins : ∀ t ∈ out.toList, insOk t = true) (hlg : cert.logs[bi]? = some (some lg)) :
    ∃ fr'', LStar fr' m fr'' m ∧ SCore f g fi cert syms fr fr'' bi k (k' + out.size) ∧
      fr''.body = R ∧ fr''.term = fr'.term ∧
      BlockFact (fun b => (trapMap f).get? b)
        (withRegs fr'' (VAt f g fi cert fr'' bi (k' + out.size) m)) (memPlus m)
        (VAt f g fi cert fr'' bi (k' + out.size) m) lg ∧
      ∀ x, Avail (wfData g (gInfo fi cert)) bi (k' + out.size) x →
        VAt f g fi cert fr'' bi (k' + out.size) m x = fr''.regs x := by
  obtain ⟨fr'', hst, h2, hb2, ht2, -, -⟩ := SCore.insList hS hm _ h hbody
    (fun t ht => by
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
      rw [insOk_renStmt]; exact hins t0 ht0)
  simp only [List.length_map, Array.length_toList] at h2
  exact ⟨fr'', hst, h2, hb2, ht2, facts_at hS hF h2.invg hm hlg⟩

/-- A replaced pure statement `v = n` (record `repl`): the target has `w` with `n`'s value. -/
theorem SCore.repl {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss R : List Stmt}
    {b : Block} {lg : BlockLog} {s' : Stmt} {w v : ValueId} {out : Array Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss)
    (hb : f.blocks[bi]? = some b) (hsk : b.body[k]? = some s)
    (hlg : cert.logs[bi]? = some (some lg)) (hl : StmtLog.repl s' w out ∈ lg.stmts)
    (hbody : fr'.body = out.toList.map (renStmt cert.subst.step) ++ R)
    (hs' : s' = renStmt cert.subst.step s) (hp : isPure s.inst = true) (hv : s.results = [v])
    (hw : cert.subst.get? v = some w) (hins : ∀ t ∈ out.toList, insOk t = true)
    (hav : Avail (wfData g (gInfo fi cert)) bi (k' + out.size) w) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + out.size) ∧ fr1'.body = R ∧
      fr1'.term = fr'.term ∧ fr1.body = ss) ∧
    (∀ c, lstep fr m ≠ .trap c) := by
  have hnc : ∀ fn args, s.inst ≠ .call fn args := by
    intro fn args he; rw [he] at hp; cases hp
  obtain ⟨-, hnt⟩ := evalInst_removable (fr := fr) (mem := m) (i := s.inst) (by simp [removable, hp])
  refine ⟨fun fr1 m1 hl1 => ?_, fun c hl1 => ?_⟩
  · rw [lstep_inst hs hnc] at hl1
    cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl1; cases hl1
    | stuck _ => rw [he] at hl1; cases hl1
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl1
      simp only [LRes.ofRes] at hl1
      split at hl1
      · rename_i regs hset
        cases hl1
        obtain ⟨hmm, a, rfl, ha⟩ := evalInst_pure hp he
        rw [hmm] at he
        obtain ⟨fr'', hst, h2, hb2, ht2, hfa, hV⟩ := h.runIns hS hF hm hbody hins hlg
        have hev : evalNode (withRegs fr'' (VAt f g fi cert fr'' bi (k' + out.size) m))
            (memPlus m) s'.inst = some a := by
          have ha' := evalNode_symsLe hp (memPlus_le m) ha
          have hr := h2.srcRename hS hb hsk hV (M := memPlus m)
          simp only [evalNode] at ha' ⊢
          split at ha'
          · rename_i r m0 he0
            cases ha'
            rw [hs', renStmt, Res.norm_eq_ok hr he0]
          · cases ha'
        have hwv := hfa.1 _ hl a hev
        rw [hV w hav] at hwv
        have hreg : regs v = some a := by
          rw [hv] at hset
          simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at hset
          subst hset; simp
        obtain ⟨hl2, h3⟩ := h2.srcOnly hS hm hs hnc he hset (by
          intro r hr
          rw [hv, List.mem_singleton] at hr
          subst hr
          rw [step_of_get hw]
          exact ⟨hav, by rw [hwv, hreg]⟩)
        exact ⟨fr'', by rw [hmm]; exact hst, h3, hb2, ht2, rfl⟩
      · cases hl1
  · rw [lstep_inst hs hnc] at hl1
    cases he : evalInst fr m s.inst with
    | trap c' => exact hnt c' he
    | stuck _ => rw [he] at hl1; cases hl1
    | ok p =>
      obtain ⟨_, _⟩ := p
      rw [he] at hl1; simp only [LRes.ofRes] at hl1; split at hl1 <;> cases hl1

end

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- A target-only result-free statement that evaluates. -/
theorem SCore.stepEmpty {fr fr' : Frame} {bi k k' : Nat} {M M2 : Mem} {t : Stmt} {ts : List Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (ht : fr'.body = t :: ts) (hr : t.results = [])
    (hnc : ∀ fn args, t.inst ≠ .call fn args) (hev : evalInst fr' M t.inst = .ok ([], M2)) :
    lstep fr' M = .next { fr' with body := ts } M2 ∧
      SCore f g fi cert syms fr { fr' with body := ts } bi k (k' + 1) := by
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  have ht0 := ht
  rw [h2] at ht
  obtain ⟨htk, -, -⟩ := drop_eq_cons ht
  have hset : fr'.regs.setMany t.results [] = some fr'.regs := by rw [hr]; rfl
  have heq : ({ fr' with regs := fr'.regs, body := ts } : Frame) = { fr' with body := ts } := rfl
  refine ⟨?_, ⟨h.invf, ?_, ?_, h.slots⟩⟩
  · rw [lstep_inst ht0 hnc]; simp only [hev, LRes.ofRes, hset]
  · have := Inv.results hS.wfg h.invg ht0 (fun ts0 h0 => evalInst_types hev h0)
      (fun hp => by obtain ⟨-, a, ha, -⟩ := evalInst_pure hp hev; cases ha) hset
    rwa [heq] at this
  · intro v hv
    obtain ⟨hav, heq', hsa⟩ := h.agree v hv
    exact ⟨hav.mono (by omega), heq', hsa⟩

end

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- A removed skeleton statement (records `skel _ remove` / `removeWithVal`): the source steps
alone, keeping memory; the replacement value (if any) is in the target. -/
theorem SCore.remove {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss R : List Stmt}
    {b : Block} {lg : BlockLog} {s' : Stmt} {o : SkelOut} {out : Array Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss)
    (hb : f.blocks[bi]? = some b) (hsk : b.body[k]? = some s)
    (hlg : cert.logs[bi]? = some (some lg)) (hl : StmtLog.skel s' o out ∈ lg.stmts)
    (hbody : fr'.body = out.toList.map (renStmt cert.subst.step) ++ R)
    (hs' : s' = renStmt cert.subst.step s) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hns : notSym s.inst = true) (hins : ∀ t ∈ out.toList, insOk t = true)
    (ho : (o = .remove ∧ s.results = []) ∨ ∃ v' r, o = .removeWithVal v' ∧ s.results = [r] ∧
      cert.subst.get? r = some v' ∧ Avail (wfData g (gInfo fi cert)) bi (k' + out.size) v') :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + out.size) ∧ fr1'.body = R ∧
      fr1'.term = fr'.term ∧ fr1.body = ss) ∧
    (∀ c, lstep fr m ≠ .trap c) := by
  obtain ⟨fr'', hst, h2, hb2, ht2, hfa, hV⟩ := h.runIns hS hF hm hbody hins hlg
  have hfact := hfa.1 _ hl
  have hr := h2.srcRename hS hb hsk hV (M := memPlus m)
  have hs'i : s'.inst = mapOperands cert.subst.step s.inst := by rw [hs']; rfl
  rw [← hs'i] at hr
  obtain ⟨hgok, hgtr⟩ := src_to_graph hns hr
  -- the fact: memory kept, no trap; `removeWithVal`: the value
  have hkeep : ∀ vs m', evalInst (withRegs fr'' (VAt f g fi cert fr'' bi (k' + out.size) m))
      (memPlus m) s'.inst = .ok (vs, m') → m' = memPlus m := by
    rcases ho with ⟨rfl, -⟩ | ⟨v', r, rfl, -⟩
    · exact hfact.1
    · exact fun vs m' he => (hfact.1 vs m' he).1
  have hnotr : ∀ c, evalInst (withRegs fr'' (VAt f g fi cert fr'' bi (k' + out.size) m))
      (memPlus m) s'.inst ≠ .trap c := by
    rcases ho with ⟨rfl, -⟩ | ⟨v', r, rfl, -⟩
    · exact hfact.2
    · exact hfact.2
  refine ⟨fun fr1 m1 hl1 => ?_, fun c hl1 => ?_⟩
  · rw [lstep_inst hs hnc] at hl1
    cases he : evalInst fr m s.inst with
    | trap c => rw [he] at hl1; cases hl1
    | stuck _ => rw [he] at hl1; cases hl1
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl1
      simp only [LRes.ofRes] at hl1
      split at hl1
      · rename_i regs hset
        cases hl1
        have hg := hgok _ _ he
        have hmm : m1 = m := mem_syms_inj (hkeep _ _ hg) (evalInst_symbols he)
        rw [hmm] at he
        obtain ⟨-, h3⟩ := h2.srcOnly hS hm hs hnc he hset (by
          intro r hr
          rcases ho with ⟨-, hres⟩ | ⟨v', r0, rfl, hres, hsub, hav⟩
          · rw [hres] at hr; cases hr
          · rw [hres, List.mem_singleton] at hr
            subst hr
            obtain ⟨a, rfl, ha⟩ := ((hfact.1 _ _ (by rw [hmm] at hg; exact hg)).2)
            rw [step_of_get hsub]
            refine ⟨hav, ?_⟩
            rw [← hV _ hav, ha]
            rw [hres] at hset
            simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at hset
            subst hset; simp)
        exact ⟨fr'', by rw [hmm]; exact hst, h3, hb2, ht2, rfl⟩
      · cases hl1
  · rw [lstep_inst hs hnc] at hl1
    cases he : evalInst fr m s.inst with
    | trap c' => exact hnotr c' (hgtr c' he)
    | stuck _ => rw [he] at hl1; cases hl1
    | ok p =>
      obtain ⟨_, _⟩ := p
      rw [he] at hl1; simp only [LRes.ofRes] at hl1; split at hl1 <;> cases hl1

end

end Opt
