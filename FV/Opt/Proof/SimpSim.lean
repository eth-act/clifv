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

theorem mem_restore' {m ma : Mem} (h : ma.symbols = (memPlus m).symbols) :
    ({ ({ ma with symbols := m.symbols } : Mem) with symbols := (memPlus m).symbols } : Mem) = ma := by
  cases ma; simp only at h ⊢; rw [h]

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

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- A skeleton statement replaced by `i` (record `skel _ (replace i)`): after the inserted
nodes, `i` steps in lock-step with the source statement. -/
theorem SCore.replace {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss R : List Stmt}
    {b : Block} {lg : BlockLog} {s' : Stmt} {i : Inst} {out pre : Array Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss)
    (hb : f.blocks[bi]? = some b) (hsk : b.body[k]? = some s)
    (hlg : cert.logs[bi]? = some (some lg)) (hl : StmtLog.skel s' (.replace i) out ∈ lg.stmts)
    (hbody : fr'.body = pre.toList.map (renStmt cert.subst.step) ++
      { results := s.results, inst := i } :: R)
    (hs' : s' = renStmt cert.subst.step s) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hns : notSym s.inst = true) (hins : ∀ t ∈ pre.toList, insOk t = true)
    (hσ : ∀ r ∈ s.results, cert.subst.step r = r) (hnci : ∀ fn args, i ≠ .call fn args)
    (hnsi : notSym i = true) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + pre.size + 1) ∧ fr1'.body = R ∧
      fr1.body = ss) ∧
    (∀ c, lstep fr m = .trap c → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c) := by
  obtain ⟨fr'', hst, h2, hb2, ht2, hfa, hV⟩ := h.runIns hS hF hm hbody hins hlg
  have hfact : ResRefines _ _ := hfa.1 _ hl
  have hr := h2.srcRename hS hb hsk hV (M := memPlus m)
  have hs'i : s'.inst = mapOperands cert.subst.step s.inst := by rw [hs']; rfl
  rw [← hs'i] at hr
  obtain ⟨hgok, hgtr⟩ := src_to_graph hns hr
  obtain ⟨b', hb', h2b, -, -⟩ := h2.invg.block
  have htk : b'.body[k' + pre.size]? = some { results := s.results, inst := i } := by
    rw [h2b] at hb2; exact (drop_eq_cons hb2).1
  have hrt := tgtGraph hS hb' htk hV (M := memPlus m)
  obtain ⟨htok, httr⟩ := graph_to_tgt hnsi hrt
  obtain ⟨hn, htr⟩ := h2.lockWith hS hm hs hb2 hσ hnc hnci
    (fun vals m1 he => htok vals m1 (evalInst_symbols he) (hfact.1 _ (hgok _ _ he)))
    (fun c he => httr c (hfact.2 c (hgtr c he)))
  refine ⟨fun fr1 m1 hl1 => ?_, fun c hl1 => ⟨fr'', m, hst, htr c hl1⟩⟩
  obtain ⟨fr1', hl', h3, hb3, hs3⟩ := hn fr1 m1 hl1
  exact ⟨fr1', hst.trans (.single hl'), h3, hb3, hs3⟩

end

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- A skeleton statement replaced by two result-free instructions (record `skel _ (two a b)`). -/
theorem SCore.two {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss R : List Stmt}
    {b : Block} {lg : BlockLog} {s' : Stmt} {a b2 : Inst} {out pre : Array Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss)
    (hb : f.blocks[bi]? = some b) (hsk : b.body[k]? = some s)
    (hlg : cert.logs[bi]? = some (some lg)) (hl : StmtLog.skel s' (.two a b2) out ∈ lg.stmts)
    (hbody : fr'.body = pre.toList.map (renStmt cert.subst.step) ++
      { inst := a } :: { inst := b2 } :: R)
    (hs' : s' = renStmt cert.subst.step s) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hns : notSym s.inst = true) (hins : ∀ t ∈ pre.toList, insOk t = true)
    (hres : s.results = []) (hnca : ∀ fn args, a ≠ .call fn args)
    (hncb : ∀ fn args, b2 ≠ .call fn args) (hnsa : notSym a = true) (hnsb : notSym b2 = true) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧
      SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + pre.size + 2) ∧ fr1'.body = R ∧
      fr1.body = ss) ∧
    (∀ c, lstep fr m = .trap c → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c) := by
  obtain ⟨fr'', hst, h2, hb2, ht2, hfa, hV⟩ := h.runIns hS hF hm hbody hins hlg
  have hfact : ResRefines _ _ := hfa.1 _ hl
  have hr := h2.srcRename hS hb hsk hV (M := memPlus m)
  have hs'i : s'.inst = mapOperands cert.subst.step s.inst := by rw [hs']; rfl
  rw [← hs'i] at hr
  obtain ⟨hgok, hgtr⟩ := src_to_graph hns hr
  obtain ⟨b', hb', h2b, -, -⟩ := h2.invg.block
  generalize VAt f g fi cert fr'' bi (k' + pre.size) m = V at hfa hV hfact hr hgok hgtr
  generalize k' + pre.size = K at h2 hV h2b ⊢
  have htka : b'.body[K]? = some { inst := a } := by
    rw [h2b] at hb2; exact (drop_eq_cons hb2).1
  have htkb : b'.body[K + 1]? = some { inst := b2 } := by
    rw [h2b] at hb2
    have := (drop_eq_cons hb2).2.1
    exact (drop_eq_cons this).1
  let fr2 : Frame := { fr'' with body := { inst := b2 } :: R }
  have hV2 : ∀ x, Avail (wfData g (gInfo fi cert)) bi (K + 1) x → V x = fr2.regs x := by
    intro x hx
    rcases avail_succ hS.wfg hb' htka hx with hr | hx'
    · cases hr
    · exact hV x hx'
  -- the graph side of `a` and `b`
  have hra := tgtGraph hS hb' htka hV (M := memPlus m)
  obtain ⟨haok, hatr⟩ := graph_to_tgt hnsa hra
  have hrb : ∀ M, evalInst (withRegs fr'' V) M b2 = evalInst fr2 M b2 := fun M =>
    tgtGraph hS hb' htkb hV2 (M := M)
  -- runs of `a` from the graph side
  have hrun_a : ∀ ma', evalInst (withRegs fr'' V) (memPlus m) a = .ok ([], ma') →
      let ma : Mem := { ma' with symbols := m.symbols }
      lstep fr'' m = .next fr2 ma ∧ SCore f g fi cert syms fr fr2 bi k (K + 1) ∧
        ({ ma with symbols := (memPlus m).symbols } : Mem) = ma' := by
    intro ma' ha
    have hsy : ma'.symbols = (memPlus m).symbols := evalInst_symbols ha
    have hres' := mem_restore' (m := m) hsy
    have hta := haok [] { ma' with symbols := m.symbols } rfl (by rw [hres']; exact ha)
    obtain ⟨hl, h3⟩ := h2.stepEmpty hS hb2 rfl hnca hta
    exact ⟨hl, h3, hres'⟩
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
        have hseq := hfact.1 _ (hgok _ _ he)
        simp only [seqEval2] at hseq
        split at hseq
        · rename_i ma' ha
          obtain ⟨hla, h3, hma⟩ := hrun_a ma' ha
          rw [← hma, hrb, evalInst_withSyms hnsb] at hseq
          obtain ⟨m0, hb0, hm0⟩ := resSyms_eq_ok hseq
          have hm0' : m0 = m1 := mem_syms_inj hm0.symm (by
            rw [evalInst_symbols hb0, evalInst_symbols he])
          rw [hm0'] at hb0
          have hvals : vals = [] := by
            have := (setMany_spec hset).1; rw [hres] at this
            exact (List.length_eq_zero_iff.1 this.symm)
          rw [hvals] at hb0 he hset
          obtain ⟨hlb, h4⟩ := h3.stepEmpty hS rfl rfl hncb hb0
          obtain ⟨-, h5⟩ := h4.srcOnly hS hm hs hnc he hset (by rw [hres]; simp)
          exact ⟨_, hst.trans (.step hla (.single hlb)), h5, rfl, rfl⟩
        all_goals cases hseq
      · cases hl1
  · rw [lstep_inst hs hnc] at hl1
    cases he : evalInst fr m s.inst with
    | ok p =>
      obtain ⟨_, _⟩ := p
      rw [he] at hl1; simp only [LRes.ofRes] at hl1; split at hl1 <;> cases hl1
    | stuck _ => rw [he] at hl1; cases hl1
    | trap c' =>
      rw [he] at hl1; cases hl1
      have hseq := hfact.2 _ (hgtr _ he)
      simp only [seqEval2] at hseq
      split at hseq
      · rename_i ma' ha
        obtain ⟨hla, -, hma⟩ := hrun_a ma' ha
        rw [← hma, hrb, evalInst_withSyms hnsb] at hseq
        have hbt := resSyms_eq_trap hseq
        refine ⟨fr2, _, hst.trans (.single hla), ?_⟩
        rw [lstep_inst (fr := fr2) rfl hncb, hbt]; rfl
      · cases hseq
      · rename_i c0 hta
        cases hseq
        refine ⟨fr'', m, hst, ?_⟩
        rw [lstep_inst hb2 hnca, hatr _ hta]; rfl
      · cases hseq

end

/-! ## Dispatch on the record -/

theorem arr_split1 {out : Array Stmt} {x : Stmt} (h : out[out.size - 1]? = some x) :
    out.toList = (out.extract 0 (out.size - 1)).toList ++ [x] := by
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 h
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_append]
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, List.length_take,
    Array.length_toList]
  split
  · rename_i hn; rw [List.getElem?_take]; simp; omega
  · rename_i hn
    rcases Nat.lt_or_ge n out.size with h1 | h1
    · have : n = out.size - 1 := by omega
      subst this; simpa using h
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem arr_split2 {out : Array Stmt} {x y : Stmt} (h2 : out.size ≥ 2)
    (hx : out[out.size - 2]? = some x) (hy : out[out.size - 1]? = some y) :
    out.toList = (out.extract 0 (out.size - 2)).toList ++ [x, y] := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_append]
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, List.length_take,
    Array.length_toList]
  split
  · rename_i hn; rw [List.getElem?_take]; simp; omega
  · rename_i hn
    rcases Nat.lt_or_ge n out.size with h1 | h1
    · rcases Nat.lt_or_ge n (out.size - 1) with h3 | h3
      · have : n = out.size - 2 := by omega
        subst this
        have e : out.size - 2 - min (out.size - 2 - 0) out.size = 0 := by omega
        rw [e]; simpa using hx
      · have : n = out.size - 1 := by omega
        subst this
        have e : out.size - 1 - min (out.size - 2 - 0) out.size = 1 := by omega
        rw [e]; simpa using hy
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem arr_all {out : Array Stmt} {p : Stmt → Bool} (h : out.all p = true) :
    ∀ t ∈ out.toList, p t = true := by
  intro t ht; rw [← Array.all_toList, List.all_eq_true] at h; exact h t ht

theorem SimpCtx.fixed_step {c : SimpCtx} {xs : List ValueId} (h : c.fixed xs = true) :
    ∀ x ∈ xs, c.subst.step x = x := by
  intro x hx
  simp only [SimpCtx.fixed, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact step_of_not_contains (h x hx)

theorem lstep_not_call {fr : Frame} {m : Mem} {s : Stmt} {ss : List Stmt} (hs : fr.body = s :: ss)
    (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    ∀ ext vals rs rest, lstep fr m ≠ .call ext vals rs rest := by
  intro ext vals rs rest hl
  obtain ⟨st, fn, args, hb, hc, -, -⟩ := lstep_call_inv hl
  rw [hs] at hb; cases hb
  exact hnc fn args hc

theorem notCall_spec {i : Inst} (h : notCall i = true) : ∀ fn args, i ≠ .call fn args := by
  intro fn args he; rw [he] at h; cases h

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- A kept call: same callee and arguments; the continuations are related. -/
theorem SCore.call {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss ts : List Stmt}
    {ext : ExtFunc} {vals : List Val} {rs : List ValueId} {rest : List Stmt}
    (h : SCore f g fi cert syms fr fr' bi k k') (hs : fr.body = s :: ss)
    (ht : fr'.body = renStmt cert.subst.step s :: ts)
    (hσ : ∀ r ∈ s.results, cert.subst.step r = r) (hl : lstep fr m = .call ext vals rs rest) :
    lstep fr' m = .call ext vals rs ts ∧ rest = ss ∧
      Cont (fun a b => SCore f g fi cert syms a b bi (k + 1) (k' + 1)) { fr with body := rest } rs
        { fr' with body := ts } rs (AbiParam.tys ext.sig.returns) := by
  obtain ⟨b, hb, h1, -, -⟩ := h.invf.block
  obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
  have hs0 := hs; have ht0 := ht
  rw [h1] at hs; rw [h2] at ht
  obtain ⟨hsk, hss, -⟩ := drop_eq_cons hs
  obtain ⟨htk, hts, -⟩ := drop_eq_cons ht
  obtain ⟨st, fn, args, hst, hc, hrs, hca⟩ := lstep_call_inv hl
  rw [hs0] at hst
  simp only [List.cons.injEq] at hst
  obtain ⟨h1s, h2s⟩ := hst
  subst h1s; subst h2s; subst hrs
  have hops : ∀ x ∈ operands s.inst, fr'.regs (cert.subst.step x) = fr.regs x :=
    fun x hx => (h.agree x (hS.wff.uses bi b hb k s hsk x hx)).2.1
  have hca' := Res.norm_eq_ok (callArgs_rename (σ := cert.subst.step) (fr := fr) (fr' := fr')
    (fn := fn) (by rw [h.invf.func, h.invg.func, hS.externs])
    (fun x hx => hops x (by rw [hc]; exact hx))) hca
  have htc : (renStmt cert.subst.step s).inst = .call fn (args.map cert.subst.step) := by
    simp [renStmt, hc, mapOperands]
  refine ⟨by rw [lstep_call ht0 htc, hca']; rfl, rfl, ?_⟩
  intro vs regs hty hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', ?_, ?_, ?_, h.slots⟩
  · have hext : sigOf f fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.invf.func] at he
      simp only [sigOf]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine Inv.results (fr := fr) (st := s) (rest := ss) hS.wff h.invf hs0 (fun ts0 h0 => ?_)
      (fun hp => by rw [hc] at hp; cases hp) hset
    rw [hc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · have hext : sigOf g fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.invf.func] at he
      simp only [sigOf, hS.externs]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine Inv.results (fr := fr') (st := renStmt cert.subst.step s) (rest := ts) hS.wfg h.invg ht0
      (fun ts0 h0 => ?_) (fun hp => by rw [htc] at hp; cases hp) hset'
    rw [htc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · exact agree_bind hS h.agree hb hb' hsk (by rw [htk]; rfl) hσ hset hset'

end

/-- A source step is matched by target steps into `P` (the obligations of `IsSim` for
statements). -/
def StepSim (fr fr' : Frame) (m : Mem) (P : Frame → Frame → Prop) : Prop :=
  (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧ P fr1 fr1') ∧
  (∀ c, lstep fr m = .trap c → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c) ∧
  (∀ ext vals rs rest, lstep fr m = .call ext vals rs rest → ∃ fr2 rs' rest', LStar fr' m fr2 m ∧
    lstep fr2 m = .call ext vals rs' rest' ∧
    Cont P { fr with body := rest } rs { fr2 with body := rest' } rs' (AbiParam.tys ext.sig.returns))

theorem StepSim.noCall {fr fr' : Frame} {m : Mem} {P : Frame → Frame → Prop} {s : Stmt}
    {ss : List Stmt} (hs : fr.body = s :: ss) (hnc : ∀ fn args, s.inst ≠ .call fn args)
    (hn : ∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧ P fr1 fr1')
    (ht : ∀ c, lstep fr m = .trap c → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c) :
    StepSim fr fr' m P :=
  ⟨hn, ht, fun ext vals rs rest hl => absurd hl (lstep_not_call hs hnc _ _ _ _)⟩

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- **One source statement**: the target runs its record. -/
theorem SRel.stmt {fr fr' : Frame} {bi k k' : Nat} {m : Mem} {s : Stmt} {ss : List Stmt}
    (h : SRel f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = s :: ss) :
    StepSim fr fr' m (fun a b => ∃ k1, SRel f g fi cert syms a b bi (k + 1) k1) := by
  obtain ⟨b, b', lg, l, hb, hb', hlg, hsk, hl, hok, hbody, hlen⟩ := h.cur hS hs
  have hlm : l ∈ lg.stmts := List.mem_of_getElem? hl
  have hmk : ∀ fr1 fr1', SCore f g fi cert syms fr1 fr1' bi (k + 1) (k' + l.out.size) →
      ∃ k1, SRel f g fi cert syms fr1 fr1' bi (k + 1) k1 := fun fr1 fr1' hc =>
    ⟨_, hc, fun lg' hlg' => by rw [hlg] at hlg'; cases hlg'; exact hlen.symm⟩
  generalize hR : (outs (lg.stmts.drop (k + 1)) ++ lg.extra.toList).map
    (renStmt cert.subst.step) = R at hbody
  have hbody' : fr'.body = l.out.toList.map (renStmt cert.subst.step) ++ R := by
    rw [hbody, ← hR]; simp [List.append_assoc]
  -- kept statements (records `keep`, `skel _ keep`)
  have hkeep : ∀ s1, l.out = #[s1] → s1 = renStmt cert.subst.step s →
      (∀ r ∈ s.results, cert.subst.step r = r) →
      StepSim fr fr' m (fun a b => ∃ k1, SRel f g fi cert syms a b bi (k + 1) k1) := by
    intro s1 hout hs1 hσ
    have ht : fr'.body = renStmt cert.subst.step s :: R := by
      rw [hbody', hout, hs1]
      simp [renStmt, mapOperands_step_idem hS.chain]
    have hsz : l.out.size = 1 := by rw [hout]; rfl
    by_cases hc : ∃ fn args, s.inst = .call fn args
    · obtain ⟨fn, args, hc⟩ := hc
      obtain ⟨hn, ht'⟩ := lstep_call_of_call (mem := m) hs hc
      refine ⟨fun fr1 m1 hl1 => absurd hl1 (hn fr1 m1), fun c hl1 => absurd hl1 (ht' c), ?_⟩
      intro ext vals rs rest hl1
      obtain ⟨hl', -, hcont⟩ := h.toSCore.call hS hs ht hσ hl1
      exact ⟨fr', rs, R, .refl _ _, hl',
        Cont.mono (fun a b' hab => hmk a b' (by rw [hsz]; exact hab)) hcont⟩
    · have hnc : ∀ fn args, s.inst ≠ .call fn args := fun fn args he => hc ⟨fn, args, he⟩
      obtain ⟨hn, htr⟩ := h.toSCore.lock hS hm hs ht hσ hnc
      refine StepSim.noCall hs hnc (fun fr1 m1 hl1 => ?_)
        (fun c hl1 => ⟨fr', m, .refl _ _, htr c hl1⟩)
      obtain ⟨fr1', hl', h1, -, -⟩ := hn fr1 m1 hl1
      exact ⟨fr1', .single hl', hmk fr1 fr1' (by rw [hsz]; exact h1)⟩
  cases l with
  | keep s1 =>
    simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx] at hok
    exact hkeep s1 rfl hok.1 (SimpCtx.fixed_step hok.2)
  | repl s1 w out =>
    simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx] at hok
    obtain ⟨⟨⟨⟨hs1, hp⟩, hins⟩, hv⟩, hav⟩ := hok
    split at hv
    · rename_i v hvr
      have hw : cert.subst.get? v = some w := by simpa using hv
      have hnc : ∀ fn args, s.inst ≠ .call fn args := by
        intro fn args he; rw [he] at hp; cases hp
      obtain ⟨hn, hnt⟩ := h.toSCore.repl hS hF hm hs hb hsk hlg hlm hbody' hs1 hp hvr hw
        (arr_all hins) (availB_sound (W := wfData g (gInfo fi cert)) hav)
      refine StepSim.noCall hs hnc (fun fr1 m1 hl1 => ?_) (fun c hl1 => absurd hl1 (hnt c))
      obtain ⟨fr1', hst, h1, -, -, -⟩ := hn fr1 m1 hl1
      exact ⟨fr1', hst, hmk fr1 fr1' h1⟩
    · cases hv
  | skel s1 o out =>
    cases o with
    | keep =>
      simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx] at hok
      obtain ⟨⟨hs1, -⟩, hout, hfix⟩ := hok
      exact hkeep s1 hout hs1 (SimpCtx.fixed_step hfix)
    | remove =>
      simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx,
        List.isEmpty_iff] at hok
      obtain ⟨⟨hs1, -⟩, ⟨⟨hnc, hns⟩, hres⟩, hins⟩ := hok
      obtain ⟨hn, hnt⟩ := h.toSCore.remove hS hF hm hs hb hsk hlg hlm hbody' hs1
        (notCall_spec hnc) hns (arr_all hins) (.inl ⟨rfl, hres⟩)
      refine StepSim.noCall hs (notCall_spec hnc) (fun fr1 m1 hl1 => ?_)
        (fun c hl1 => absurd hl1 (hnt c))
      obtain ⟨fr1', hst, h1, -, -, -⟩ := hn fr1 m1 hl1
      exact ⟨fr1', hst, hmk fr1 fr1' h1⟩
    | removeWithVal v' =>
      simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx] at hok
      obtain ⟨⟨hs1, -⟩, ⟨⟨⟨hnc, hns⟩, hins⟩, hav⟩, hr⟩ := hok
      split at hr
      · rename_i r hrr
        have hsub : cert.subst.get? r = some v' := by simpa using hr
        obtain ⟨hn, hnt⟩ := h.toSCore.remove hS hF hm hs hb hsk hlg hlm hbody' hs1
          (notCall_spec hnc) hns (arr_all hins)
          (.inr ⟨v', r, rfl, hrr, hsub, availB_sound (W := wfData g (gInfo fi cert)) hav⟩)
        refine StepSim.noCall hs (notCall_spec hnc) (fun fr1 m1 hl1 => ?_)
          (fun c hl1 => absurd hl1 (hnt c))
        obtain ⟨fr1', hst, h1, -, -, -⟩ := hn fr1 m1 hl1
        exact ⟨fr1', hst, hmk fr1 fr1' h1⟩
      · cases hr
    | replace i =>
      simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx,
        decide_eq_true_eq] at hok
      obtain ⟨⟨hs1, -⟩, ⟨⟨⟨⟨⟨⟨⟨⟨hnc, hns⟩, hfr⟩, hfi⟩, hsz⟩, hpre⟩, hlast⟩, hnci⟩, hnsi⟩⟩ := hok
      have hsplit := arr_split1 hlast
      have hti : mapOperands cert.subst.step i = i := by
        conv => rhs; rw [← mapOperands_id i]
        exact mapOperands_congr (SimpCtx.fixed_step hfi)
      have hb2 : fr'.body = (out.extract 0 (out.size - 1)).toList.map (renStmt cert.subst.step) ++
          { results := s.results, inst := i } :: R := by
        rw [hbody', show (StmtLog.skel s1 (.replace i) out).out = out from rfl, hsplit]
        simp [renStmt, hti]
      obtain ⟨hn, htr⟩ := h.toSCore.replace hS hF hm hs hb hsk hlg hlm hb2 hs1 (notCall_spec hnc)
        hns (arr_all hpre) (SimpCtx.fixed_step hfr) (notCall_spec hnci) hnsi
      refine StepSim.noCall hs (notCall_spec hnc) (fun fr1 m1 hl1 => ?_) htr
      obtain ⟨fr1', hst, h1, -, -⟩ := hn fr1 m1 hl1
      refine ⟨fr1', hst, hmk fr1 fr1' ?_⟩
      have : k' + (out.extract 0 (out.size - 1)).size + 1 =
          k' + (StmtLog.skel s1 (.replace i) out).out.size := by
        simp only [StmtLog.out, Array.size_extract]; omega
      rw [← this]; exact h1
    | two a b2 =>
      simp only [SimpCtx.stmtOk, Bool.and_eq_true, beq_iff_eq, SimpCtx.σ, sctx,
        decide_eq_true_eq, List.isEmpty_iff] at hok
      obtain ⟨⟨hs1, -⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnc, hns⟩, hfab⟩, hres⟩, hsz⟩, hpre⟩, hxa⟩, hxb⟩, hnca⟩, hncb⟩,
        hnsa⟩, hnsb⟩⟩ := hok
      have hsplit := arr_split2 hsz hxa hxb
      have hfa := SimpCtx.fixed_step hfab
      have hta : mapOperands cert.subst.step a = a := by
        conv => rhs; rw [← mapOperands_id a]
        exact mapOperands_congr (fun x hx => hfa x (List.mem_append_left _ hx))
      have htb : mapOperands cert.subst.step b2 = b2 := by
        conv => rhs; rw [← mapOperands_id b2]
        exact mapOperands_congr (fun x hx => hfa x (List.mem_append_right _ hx))
      have hb2 : fr'.body = (out.extract 0 (out.size - 2)).toList.map (renStmt cert.subst.step) ++
          { inst := a } :: { inst := b2 } :: R := by
        rw [hbody', show (StmtLog.skel s1 (.two a b2) out).out = out from rfl, hsplit]
        simp [renStmt, hta, htb]
      obtain ⟨hn, htr⟩ := h.toSCore.two hS hF hm hs hb hsk hlg hlm hb2 hs1 (notCall_spec hnc)
        hns (arr_all hpre) hres (notCall_spec hnca) (notCall_spec hncb) hnsa hnsb
      refine StepSim.noCall hs (notCall_spec hnc) (fun fr1 m1 hl1 => ?_) htr
      obtain ⟨fr1', hst, h1, -, -⟩ := hn fr1 m1 hl1
      refine ⟨fr1', hst, hmk fr1 fr1' ?_⟩
      have : k' + (out.extract 0 (out.size - 2)).size + 2 =
          k' + (StmtLog.skel s1 (.two a b2) out).out.size := by
        simp only [StmtLog.out, Array.size_extract]; omega
      rw [← this]; exact h1

end

/-! ## Branches -/

/-- The block call a branch takes. -/
def pick (fr : Frame) : Terminator → Res BlockCall
  | .jump d => .ok d
  | .brif c t e => fr.get c >>= fun cv => .ok (if Sem.truthy cv.bits then t else e)
  | .brTable x d tbl => fr.get x >>= fun xv => .ok (tbl[xv.toNat]?.getD d)
  | _ => .stuck "not a branch"

theorem termEval_pick {fr : Frame} {M : Mem} {t : Terminator} (ht : isBranch t = true) :
    termEval fr M t = (pick fr t >>= fun d => fr.getMany d.args >>= fun vs => pure (d.block, vs, M)) := by
  cases t <;> simp only [isBranch] at ht <;> (try cases ht) <;> simp only [termEval, pick]
  · rfl
  · cases fr.get _ <;> rfl
  · cases fr.get _ <;> rfl

theorem lstep_pick {fr : Frame} {M : Mem} (hb : fr.body = []) (ht : isBranch fr.term = true) :
    lstep fr M = LRes.ofRes (pick fr fr.term) fun d =>
      LRes.ofRes (enterBlock fr d) fun fr' => .next fr' M := by
  rw [lstep_term hb]
  cases hT : fr.term <;> rw [hT] at ht <;> simp only [isBranch] at ht <;> (try cases ht) <;>
    simp only [pick]
  · rfl
  · cases fr.get _ <;> rfl
  · cases fr.get _ <;> rfl

theorem pick_succ {fr : Frame} {t : Terminator} {d : BlockCall} (h : pick fr t = .ok d) :
    d.block ∈ termSuccs t ∧ ∀ x ∈ d.args, x ∈ termOperands t := by
  cases t <;> simp only [pick] at h
  · cases h; simp [termSuccs, termOperands]
  · rename_i c th el
    simp only [Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨cv, -, hd⟩ := h
    subst hd
    split
    · exact ⟨by simp [termSuccs], fun x hx => by simp [termOperands, hx]⟩
    · exact ⟨by simp [termSuccs], fun x hx => by simp [termOperands, hx]⟩
  · rename_i x dflt tbl
    simp only [Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨xv, -, hd⟩ := h
    subst hd
    cases hq : tbl[xv.toNat]? with
    | none =>
      simp only [Option.getD_none]
      exact ⟨by simp [termSuccs], fun y hy => by simp [termOperands, hy]⟩
    | some q =>
      simp only [Option.getD_some]
      have hm := List.mem_of_getElem? hq
      exact ⟨by simp only [termSuccs, List.mem_cons, List.mem_map]; exact .inr ⟨_, hm, rfl⟩,
        fun y hy => by simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
                       exact .inr ⟨_, hm, hy⟩⟩
  all_goals cases h

theorem pick_congr {fr fr' : Frame} {t : Terminator}
    (hr : ∀ x ∈ termOperands t, fr'.regs x = fr.regs x) : pick fr' t = pick fr t := by
  cases t <;> simp only [pick]
  · rename_i c _ _
    have : fr'.get c = fr.get c := by simp only [Frame.get, hr c (by simp [termOperands])]
    rw [this]
  · rename_i x _ _
    have : fr'.get x = fr.get x := by simp only [Frame.get, hr x (by simp [termOperands])]
    rw [this]

theorem pick_rename {σ : ValueId → ValueId} {fr fr' : Frame} {t : Terminator} {d : BlockCall}
    (hr : ∀ x ∈ termOperands t, fr'.regs (σ x) = fr.regs x) (h : pick fr t = .ok d) :
    pick fr' (mapTerm σ t) = .ok (mapBlockCall σ d) := by
  cases t <;> simp only [pick, mapTerm] at h ⊢
  · cases h; rfl
  · rename_i c th el
    simp only [Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨cv, hc, hd⟩ := h
    subst hd
    have : fr'.get (σ c) = .ok cv := by
      simp only [Frame.get, Res.ofOption_eq_ok] at hc ⊢
      rw [hr c (by simp [termOperands]), hc]
    rw [this]
    simp only [Res.ok_bind]
    split <;> rfl
  · rename_i x dflt tbl
    simp only [Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨xv, hc, hd⟩ := h
    subst hd
    have : fr'.get (σ x) = .ok xv := by
      simp only [Frame.get, Res.ofOption_eq_ok] at hc ⊢
      rw [hr x (by simp [termOperands]), hc]
    rw [this]
    simp only [Res.ok_bind]
    rw [List.getElem?_map]; cases tbl[xv.toNat]? <;> rfl
  all_goals cases h

theorem pick_ne_trap (fr : Frame) (t : Terminator) (c : TrapCode) : pick fr t ≠ .trap c := by
  cases t <;> simp only [pick] <;> (try (intro h; cases h)) <;>
    (intro h; simp only [Res.bind_eq_trap, Frame.get_ne_trap, false_or] at h;
     obtain ⟨_, _, h⟩ := h; cases h)

/-- The source leaves its block by a branch. -/
theorem lstep_branch {fr fr1 : Frame} {M M1 : Mem} (hb : fr.body = []) (ht : isBranch fr.term = true)
    (h : lstep fr M = .next fr1 M1) :
    M1 = M ∧ ∃ d, pick fr fr.term = .ok d ∧ enterBlock fr d = .ok fr1 := by
  rw [lstep_pick hb ht] at h
  cases hp : pick fr fr.term with
  | ok d =>
    rw [hp] at h
    simp only [LRes.ofRes] at h
    cases he : enterBlock fr d with
    | ok fr1' => rw [he] at h; simp only [LRes.ofRes, LRes.next.injEq] at h
                 obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, d, rfl, he⟩
    | trap _ => rw [he] at h; cases h
    | stuck _ => rw [he] at h; cases h
  | trap _ => rw [hp] at h; cases h
  | stuck _ => rw [hp] at h; cases h

/-- `termEval` does not touch memory. -/
theorem termEval_mem {fr : Frame} {M M' : Mem} {t : Terminator} {bid : BlockId} {vs : List Val}
    {x : Mem} (h : termEval fr M t = .ok (bid, vs, x)) :
    x = M ∧ termEval fr M' t = .ok (bid, vs, M') := by
  cases t <;> simp only [termEval, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  · obtain ⟨a, ha, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩; simp only [termEval, ha]; rfl
  · obtain ⟨a, ha, b, hb, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩; simp only [termEval, ha, Res.ok_bind, hb]; rfl
  · obtain ⟨a, ha, b, hb, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩; simp only [termEval, ha, Res.ok_bind, hb]; rfl
  all_goals simp [bind, Res.bind] at h

theorem termEval_trapc {fr : Frame} {M : Mem} {t : Terminator} {c : TrapCode}
    (h : termEval fr M t = .trap c) : t = .trap c := by
  cases t <;> simp only [termEval, Res.bind_eq_trap, getMany_not_trap, Frame.get_ne_trap,
    false_or] at h
  all_goals first
    | (obtain ⟨_, _, h⟩ := h; simp [Res.bind_eq_trap, getMany_not_trap, pure] at h)
    | (cases h; rfl)
    | (simp [pure, bind, Res.bind] at h)
  all_goals (obtain ⟨_, _, h⟩ := h; simp only [Res.bind_eq_trap] at h
             rcases h with h | ⟨_, _, h⟩
             · exact absurd h (getMany_not_trap _ _ _)
             · cases h)

/-- The trap blocks of `f`. -/
theorem trapMap_spec {f : Function} {bid : BlockId} {c : TrapCode}
    (h : (trapMap f).get? bid = some c) :
    ∃ blk ∈ f.blocks, blk.id = bid ∧ trapBlock? blk = some c := by
  have key : ∀ (l : List Block) (m0 : Std.HashMap BlockId TrapCode),
      (l.foldl (fun m b => match trapBlock? b with
        | some c => m.insert b.id c | none => m) m0).get? bid = some c →
      m0.get? bid = some c ∨ ∃ blk ∈ l, blk.id = bid ∧ trapBlock? blk = some c := by
    intro l
    induction l with
    | nil => intro m0 h; exact .inl h
    | cons b bs ih =>
      intro m0 h
      rcases ih _ h with h1 | ⟨blk, hm, h2⟩
      · cases ht : trapBlock? b with
        | none => simp only [ht] at h1; exact .inl h1
        | some c' =>
          simp only [ht] at h1
          rw [hm_get?_insert] at h1
          split at h1
          · rename_i he; cases h1; exact .inr ⟨b, by simp, he, ht⟩
          · exact .inl h1
      · exact .inr ⟨blk, by simp [hm], h2⟩
  rcases key f.blocks {} h with h1 | h2
  · simp at h1
  · exact h2

theorem trapBlock?_spec {blk : Block} {c : TrapCode} (h : trapBlock? blk = some c) :
    blk.term = .trap c ∧ ∀ s ∈ blk.body, isPure s.inst = true := by
  simp only [trapBlock?] at h
  split at h
  · rename_i c' ht
    split at h
    · rename_i hp; cases h
      simp only [List.all_eq_true] at hp
      exact ⟨ht, hp⟩
    · cases h
  · cases h

/-- The effect instructions of a list of extra statements. -/
def effsL (E : List Stmt) : List Inst := E.filterMap fun t => if insOk t then none else some t.inst

theorem effsOf_eq (extra : Array Stmt) : effsOf extra = effsL extra.toList := rfl

theorem trapOk_spec {t : Stmt} (h : trapOk t = true) :
    t.results = [] ∧ ∃ y code, t.inst = .trapz y code ∨ t.inst = .trapnz y code := by
  simp only [trapOk, Bool.and_eq_true, List.isEmpty_iff] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hti : t.inst <;> rw [hti] at h2 <;> (try cases h2)
  · rename_i y code; exact ⟨y, code, .inl rfl⟩
  · rename_i y code; exact ⟨y, code, .inr rfl⟩

theorem insOk_trapOk {t : Stmt} (h : trapOk t = true) : insOk t = false := by
  obtain ⟨hr, -⟩ := trapOk_spec h
  simp [insOk, hr]

/-- A conditional trap reads one register and keeps memory. -/
theorem evalInst_trapLike {fr fr' : Frame} {M M' : Mem} {i : Inst} {y : ValueId} {code : TrapCode}
    (hi : i = .trapz y code ∨ i = .trapnz y code) (hy : fr'.regs y = fr.regs y) :
    (∀ vs M1, evalInst fr M i = .ok (vs, M1) → vs = [] ∧ M1 = M ∧ evalInst fr' M' i = .ok ([], M')) ∧
    (∀ c, evalInst fr M i = .trap c → ∀ M'', evalInst fr' M'' i = .trap c) := by
  have hg : fr'.get y = fr.get y := by simp only [Frame.get, hy]
  rcases hi with rfl | rfl
  all_goals
    simp only [evalInst, hg]
    refine ⟨fun vs M1 h => ?_, fun c h M'' => ?_⟩ <;>
    cases hc : fr.get y <;> rw [hc] at h <;> (try rw [hc]) <;>
    simp only [Res.ok_bind, Res.trap_bind, Res.stuck_bind, reduceCtorEq] at h ⊢ <;>
    (try split at h) <;> (try split) <;> simp_all [pure]

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- The target runs the extra statements of a terminator record: inserted pure nodes (whose
values are the graph's) and conditional traps (as in `effTerm`). -/
theorem SCore.runExtras {fr : Frame} {bi k : Nat} {m : Mem} (hm : m.symbols = syms)
    {fr0 : Frame} {ρ : Valuation} (T : Terminator) :
    ∀ (E : List Stmt) {fr' : Frame} {K : Nat}, SCore f g fi cert syms fr fr' bi k K →
      fr'.body = E.map (renStmt cert.subst.step) →
      (∀ t ∈ E, insOk t = true ∨
        (trapOk t = true ∧ ∀ x ∈ operands t.inst, cert.subst.step x = x)) →
      fr0.func = fr'.func → fr0.slots = fr'.slots →
      (∀ x, Avail (wfData g (gInfo fi cert)) bi K x →
        den cert.graph ρ fr0 (memPlus m) x = fr'.regs x) →
      (∃ fr2 K2, LStar fr' m fr2 m ∧ fr2.body = [] ∧ SCore f g fi cert syms fr fr2 bi k K2 ∧
        fr2.func = fr'.func ∧ fr2.slots = fr'.slots ∧ fr2.term = fr'.term ∧
        (∀ x, Avail (wfData g (gInfo fi cert)) bi K2 x →
          den cert.graph ρ fr0 (memPlus m) x = fr2.regs x) ∧
        effTerm (withRegs fr0 (den cert.graph ρ fr0 (memPlus m))) (memPlus m) (effsL E) T =
          termEval (withRegs fr0 (den cert.graph ρ fr0 (memPlus m))) (memPlus m) T) ∨
      (∃ fr2 c, LStar fr' m fr2 m ∧ (∀ m', lstep fr2 m' = .trap c) ∧
        effTerm (withRegs fr0 (den cert.graph ρ fr0 (memPlus m))) (memPlus m) (effsL E) T = .trap c)
  | [], fr', K, h, hb, _, _, _, hV => .inl ⟨fr', K, .refl _ _, by simpa using hb, h, rfl, rfl, rfl,
      hV, rfl⟩
  | t :: E, fr', K, h, hb, hE, hf0, hs0, hV => by
    obtain ⟨b', hb', h2, -, -⟩ := h.invg.block
    have hb1 : fr'.body = renStmt cert.subst.step t :: E.map (renStmt cert.subst.step) := by
      rw [hb]; rfl
    have htk : b'.body[K]? = some (renStmt cert.subst.step t) := by
      rw [h2] at hb1; exact (drop_eq_cons hb1).1
    have hmemt : renStmt cert.subst.step t ∈ b'.body := List.mem_of_getElem? htk
    rcases hE t (by simp) with hins | ⟨htr, hfix⟩
    · -- an inserted pure node
      have hins' : insOk (renStmt cert.subst.step t) = true := by rw [insOk_renStmt]; exact hins
      obtain ⟨hp, u, a, hu, hev⟩ := h.insEval hS (m := m) hb1 hins'
      obtain ⟨hl, h1⟩ := h.tpure hS hm hb1 hp hu hev
      have heff : effsL (t :: E) = effsL E := by simp [effsL, hins]
      rw [heff]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpure, -⟩ := hS.gblock hb'
      have hD := hpure _ hmemt u hu hp
      have hV1 : ∀ x, Avail (wfData g (gInfo fi cert)) bi (K + 1) x →
          den cert.graph ρ fr0 (memPlus m) x = (fr'.regs.set u a) x := by
        intro x hx
        rcases avail_succ hS.wfg hb' htk hx with hr | hx'
        · rw [hu, List.mem_singleton] at hr
          subst hr
          simp only [Regs.set_same]
          rw [den_node (D := cert.graph) hD]
          have hsy : SymsLe m (memPlus m) := memPlus_le m
          rw [← evalNode_symsLe hp hsy hev]
          refine evalNode_congr (by simp only [hf0]) (by simp only [hs0]) ?_
          intro y hy
          exact hV y (hS.wfg.uses bi b' hb' K _ htk y hy)
        · have hnr := avail_not_result hS.wfg hb' htk hx'
          rw [hu, List.mem_singleton] at hnr
          rw [Regs.set_other _ _ hnr]; exact hV x hx'
      rcases SCore.runExtras hm T E h1 rfl (fun t' ht' => hE t' (by simp [ht'])) hf0 hs0 hV1 with
        ⟨fr2, K2, hst, hb2, h3, hf2, hs2, ht2, hV2, he2⟩ | ⟨fr2, c, hst, htr2, he2⟩
      · exact .inl ⟨fr2, K2, .step hl hst, hb2, h3, hf2, hs2, ht2, hV2, he2⟩
      · exact .inr ⟨fr2, c, .step hl hst, htr2, he2⟩
    · -- a conditional trap
      obtain ⟨hr, y, code, hi⟩ := trapOk_spec htr
      have hti : (renStmt cert.subst.step t).inst = t.inst := by
        simp only [renStmt]
        conv => rhs; rw [← mapOperands_id t.inst]
        exact mapOperands_congr hfix
      have hyops : y ∈ operands t.inst := by rcases hi with hi | hi <;> simp [hi, operands]
      have hyav := hS.wfg.uses bi b' hb' K _ htk y (by rw [hti]; exact hyops)
      have hnc : ∀ fn args, (renStmt cert.subst.step t).inst ≠ .call fn args := by
        rw [hti]; rcases hi with hi | hi <;> rw [hi] <;> intro fn args he <;> cases he
      have heff : effsL (t :: E) = t.inst :: effsL E := by
        simp [effsL, insOk_trapOk htr]
      rw [heff]
      obtain ⟨hok, htrp⟩ := evalInst_trapLike (fr := fr') (fr' := withRegs fr0
        (den cert.graph ρ fr0 (memPlus m))) (M := m) (M' := memPlus m) hi (hV y hyav)
      obtain ⟨a, ha, -⟩ := h.invg.regs y hyav
      cases he : evalInst fr' m t.inst with
      | ok p =>
        obtain ⟨vs, M1⟩ := p
        obtain ⟨rfl, hM1, hF⟩ := hok vs M1 he
        rw [hM1] at he
        rw [hti] at hnc
        have hr' : (renStmt cert.subst.step t).results = [] := hr
        obtain ⟨hl, h1⟩ := h.stepEmpty hS hb1 hr' (by rw [hti]; exact hnc) (by rw [hti]; exact he)
        have hV1 : ∀ x, Avail (wfData g (gInfo fi cert)) bi (K + 1) x →
            den cert.graph ρ fr0 (memPlus m) x = fr'.regs x := by
          intro x hx
          rcases avail_succ hS.wfg hb' htk hx with hr2 | hx'
          · rw [hr'] at hr2; cases hr2
          · exact hV x hx'
        simp only [effTerm, hF]
        rcases SCore.runExtras hm T E h1 rfl (fun t' ht' => hE t' (by simp [ht'])) hf0 hs0 hV1 with
          ⟨fr2, K2, hst, hb2, h3, hf2, hs2, ht2, hV2, he2⟩ | ⟨fr2, c, hst, htr2, he2⟩
        · exact .inl ⟨fr2, K2, .step hl hst, hb2, h3, hf2, hs2, ht2, hV2, he2⟩
        · exact .inr ⟨fr2, c, .step hl hst, htr2, he2⟩
      | trap c =>
        refine .inr ⟨fr', c, .refl _ _, fun m' => ?_, ?_⟩
        · rw [lstep_inst hb1 hnc, hti]
          have := (evalInst_trapLike (fr := fr') (fr' := fr') (M := m) (M' := m') hi rfl).2 c he m'
          rw [this]; rfl
        · simp only [effTerm, htrp c he]
      | stuck msg =>
        exfalso
        rcases hi with hi | hi <;> rw [hi] at he <;>
          simp only [evalInst, Frame.get, ha, Res.ofOption_some, Res.ok_bind] at he <;>
          split at he <;> cases he

end

/-! ## Block entry -/

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

theorem SOk.block?_corr {id : BlockId} {j : Nat} {b b' : Block} (hf : f.block? id = some b)
    (hj : f.blocks[j]? = some b) (hj' : g.blocks[j]? = some b') : g.block? id = some b' := by
  obtain ⟨j0, hj0, hid⟩ := block?_index hS.wff hf
  have := idx_unique hS.wff hj0 hj rfl
  subst this
  rw [Function.block?, List.find?_eq_some_iff_getElem] at hf ⊢
  obtain ⟨hp, i, hi, hbi, hlt⟩ := hf
  have hij : i = j0 := idx_unique hS.wff (by simp [hi, hbi]) hj0 rfl
  subst hij
  obtain ⟨b'', -, hb'', -, hid', -⟩ := hS.blocks i b hj0
  rw [hj'] at hb''; cases hb''
  have hi' : i < g.blocks.length := (List.getElem?_eq_some_iff.1 hj').1
  refine ⟨by simpa [hid'] using hp, i, hi', by simpa [hi'] using hj', fun j2 hj2 => ?_⟩
  have hj2f : j2 < f.blocks.length := by omega
  obtain ⟨b2, -, hb2, -, hid2, -⟩ := hS.blocks j2 f.blocks[j2] (by simp [hj2f])
  have := hlt j2 hj2
  simp only [List.getElem?_eq_getElem (show j2 < g.blocks.length by omega), Option.some.injEq]
    at hb2
  rw [hb2, hid2]; exact this

/-- Both frames enter corresponding blocks with the same arguments. -/
theorem SCore.enter {fr fr' fr1 : Frame} {bi k k' : Nat} {d d' : BlockCall} {vs : List Val}
    (h : SCore f g fi cert syms fr fr' bi k k') (hs : fr.body = []) (ht : fr'.body = [])
    (hd : d.block ∈ termSuccs fr.term) (he : enterBlock fr d = .ok fr1)
    (hd' : d'.block ∈ termSuccs fr'.term) (hblk : d'.block = d.block)
    (hga : fr.getMany d.args = .ok vs) (hga' : fr'.getMany d'.args = .ok vs) :
    ∃ fr1', enterBlock fr' d' = .ok fr1' ∧ ∃ j, SRel f g fi cert syms fr1 fr1' j 0 0 := by
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := Inv.enter hS.wff h.invf hs hd he
  obtain ⟨b2x, args, regs, hb2x, hga0, hty, hset, rfl⟩ := enterBlock_ok he
  rw [h.invf.func, hb2] at hb2x; cases hb2x
  rw [hga] at hga0; cases hga0
  obtain ⟨b2', lg2, hj', hlg2, hid2, hpar2, -, -, -, -, -, hps, -⟩ := hS.blocks j b2 hj
  have hgb : fr'.func.block? d'.block = some b2' := by
    rw [h.invg.func, hblk]; exact hS.block?_corr hb2 hj hj'
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := b2'.params.map (·.1)) (vs := vs)
    (by rw [hpar2]; exact (setMany_spec hset).1)
  have he' : enterBlock fr' d' = .ok ⟨fr'.func, regs', fr'.slots, b2'.body, b2'.term⟩ :=
    enterBlock_of hgb hga' (by rw [hpar2]; exact hty) hset'
  refine ⟨_, he', j, ⟨?_, fun lg hlg => by simp [outs]⟩⟩
  obtain ⟨jx, b3, hj3, hb3, hinv2⟩ := Inv.enter hS.wfg h.invg ht hd' he'
  have : b3 = b2' := by
    rw [h.invg.func] at hgb; rw [hgb] at hb3; exact (Option.some.inj hb3).symm
  subst b3
  have : jx = j := idx_unique hS.wfg hj3 hj' rfl
  subst jx
  refine ⟨hinv1, hinv2, ?_, h.slots⟩
  intro v hv
  by_cases hdv : (wfData f fi).dm v = some (j, 0)
  · obtain ⟨b4, p, hb4, hp, hpv⟩ := site_param' hS.wff hdv
    rw [hj] at hb4; cases hb4
    have hσv : cert.subst.step v = v := by
      rw [← hpv]; exact step_of_not_contains (hps p hp).2.2
    rw [hσv]
    have hvm : v ∈ b2.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
    have hgs : (wfData g (gInfo fi cert)).dm v = some (j, 0) := by
      rw [← hpv]; exact site_param hS.wfg hj' (by rw [hpar2]; exact hp)
    refine ⟨⟨j, 0, hgs, .inl ⟨rfl, Nat.le_refl _⟩⟩, ?_, ?_⟩
    · rw [hpar2] at hset'
      exact (setMany_same hset hset' v hvm).symm
    · intro d0 t0 hd0
      rw [hdv] at hd0; simp only [Option.some.injEq, Prod.mk.injEq] at hd0
      obtain ⟨rfl, -⟩ := hd0
      exact ⟨j, 0, by rw [hσv]; exact hgs, .refl _⟩
  · have hbid : b2.id = d.block := by obtain ⟨_, _, h0⟩ := block?_index hS.wff hb2; exact h0
    obtain ⟨b, hb, -, hterm, -⟩ := h.invf.block
    have hvp := avail_pred hS.wff hb hj (by rw [hbid, ← hterm]; exact hd) hv hdv
    have hkk : k = b.body.length := by
      obtain ⟨b0, hb0, h1, -, hk⟩ := h.invf.block
      rw [hb] at hb0; cases hb0
      rw [hs] at h1
      have := List.drop_eq_nil_iff.1 h1.symm; omega
    rw [← hkk] at hvp
    obtain ⟨-, heq, hsa⟩ := h.agree v hvp
    obtain ⟨d, t, hd0, hva⟩ := hv
    rcases hva with ⟨hdj, ht0⟩ | ⟨hne, ha⟩
    · exact absurd (by rw [hd0, hdj, show t = 0 by omega]) hdv
    obtain ⟨d', t', hd', hanc⟩ := hsa d t hd0
    have hne2 : d' ≠ j := fun he => hne (Anc.antisymm hS.wff.rank ha (he ▸ hanc))
    refine ⟨⟨d', t', hd', .inr ⟨hne2, hanc.trans ha⟩⟩, ?_, hsa⟩
    have hn1 : cert.subst.step v ∉ b2'.params.map (·.1) := by
      intro hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      have := site_param hS.wfg hj' hp
      rw [hpv, hd'] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact hne2 this.1
    have hn2 : v ∉ b2.params.map (·.1) := by
      intro hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      exact hdv (by rw [← hpv]; exact site_param hS.wff hj hp)
    simp only
    rw [((setMany_spec hset').2 _).1 hn1, ((setMany_spec hset).2 _).1 hn2, heq]

end

/-! ## Terminators -/

/-- The source stopped on its way to a trap block: it runs pure statements, then traps with
`c`; the target is already stopped at a trap with `c`. -/
def Frozen (f g : Function) (fr fr' : Frame) : Prop :=
  ∃ c, fr.func = f ∧ fr'.func = g ∧ fr'.slots = fr.slots ∧ fr.term = .trap c ∧
    (∀ s ∈ fr.body, isPure s.inst = true) ∧ ∀ m, lstep fr' m = .trap c

/-- The relation of the simplify simulation. -/
def SSR (f g : Function) (fi : Info) (cert : SimpCert) (syms : String → Option Nat)
    (fr fr' : Frame) : Prop :=
  (∃ bi k k', SRel f g fi cert syms fr fr' bi k k') ∨ Frozen f g fr fr'

theorem termEval_isBranch {fr : Frame} {M : Mem} {t : Terminator} {r : BlockId × List Val × Mem}
    (h : termEval fr M t = .ok r) : isBranch t = true := by
  cases t <;> simp only [isBranch] <;> simp [termEval] at h
  all_goals (simp [bind, Res.bind] at h)

theorem block_unique {f : Function} {W : WfData} (hW : Wf f W) {blk blk' : Block} {bid : BlockId}
    (hm : blk ∈ f.blocks) (hid : blk.id = bid) (h : f.block? bid = some blk') : blk = blk' := by
  obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.1 hm
  obtain ⟨j, hj, hid'⟩ := block?_index hW h
  have := idx_unique hW hj0 hj (by rw [hid, hid'])
  subst this
  rw [hj0] at hj; exact Option.some.inj hj

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- **The terminator**: the target runs the extra statements and its (rewritten) terminator. -/
theorem SRel.term {fr fr' : Frame} {bi k k' : Nat} {m : Mem}
    (h : SRel f g fi cert syms fr fr' bi k k') (hm : m.symbols = syms) (hs : fr.body = []) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', LStar fr' m fr1' m1 ∧
      SSR f g fi cert syms fr1 fr1') ∧
    (∀ c, lstep fr m = .trap c → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c) ∧
    (∀ vals, lstep fr m = .ret vals → ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals → ∃ fr2, LStar fr' m fr2 m ∧
      lstep fr2 m = .tail ext vals) := by
  obtain ⟨b, b', lg, hb, hb', hlg, hterm, ht', hlt, htok, hbody, hkk, hid, hpar⟩ := h.atEnd hS hs
  have hops : ∀ x ∈ termOperands fr.term, fr'.regs (cert.subst.step x) = fr.regs x := by
    intro x hx
    rw [hterm] at hx
    have := hS.wff.termUses bi b hb x hx
    rw [← hkk] at this
    exact (h.agree x this).2.1
  have hbr : isBranch lg.term = isBranch b.term := by rw [hlt]; cases b.term <;> rfl
  by_cases hB : isBranch b.term = true
  · -- a branch
    have hsrc_nt : ∀ c, lstep fr m ≠ .trap c := by
      intro c hl
      rw [lstep_pick hs (by rw [hterm]; exact hB)] at hl
      cases hp : pick fr fr.term with
      | ok d =>
        rw [hp] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr d with
        | ok _ => rw [he] at hl; cases hl
        | trap c' => exact enterBlock_not_trap _ _ _ he
        | stuck _ => rw [he] at hl; cases hl
      | trap c' => exact pick_ne_trap _ _ _ hp
      | stuck _ => rw [hp] at hl; cases hl
    refine ⟨fun fr1 m1 hl => ?_, fun c hl => absurd hl (hsrc_nt c), fun vals hl => ?_,
      fun ext vals hl => ?_⟩
    rotate_left
    · rw [lstep_pick hs (by rw [hterm]; exact hB)] at hl
      cases hp : pick fr fr.term with
      | ok d =>
        rw [hp] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr d <;> rw [he] at hl <;> cases hl
      | trap _ => rw [hp] at hl; cases hl
      | stuck _ => rw [hp] at hl; cases hl
    · rw [lstep_pick hs (by rw [hterm]; exact hB)] at hl
      cases hp : pick fr fr.term with
      | ok d =>
        rw [hp] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr d <;> rw [he] at hl <;> cases hl
      | trap _ => rw [hp] at hl; cases hl
      | stuck _ => rw [hp] at hl; cases hl
    obtain ⟨hmm, d, hpd, he⟩ := lstep_branch hs (by rw [hterm]; exact hB) hl
    rw [hmm]
    obtain ⟨blk, vs, regs, hblk, hga, hty, hset, rfl⟩ := enterBlock_ok he
    obtain ⟨hfa, hV⟩ := facts_at hS hF h.invg hm hlg
    generalize hVd : VAt f g fi cert fr' bi k' m = V at hfa hV
    -- the source branch, read in the graph valuation
    have hrop : ∀ x ∈ termOperands b.term, (withRegs fr' V).regs (cert.subst.step x) = fr.regs x := by
      intro x hx
      have hx' : x ∈ termOperands fr.term := by rw [hterm]; exact hx
      have hav := (h.agree x (by
        have := hS.wff.termUses bi b hb x hx; rw [← hkk] at this; exact this)).1
      simp only [withRegs]; rw [hV _ hav]; exact hops x hx'
    have hpd' := pick_rename hrop (by rw [← hterm]; exact hpd)
    have hgm : (withRegs fr' V).getMany (d.args.map cert.subst.step) = .ok vs := by
      have hr := getMany_rename (σ := cert.subst.step) (fr := fr) (fr' := withRegs fr' V)
        (xs := d.args) (fun x hx => hrop x (by
          have := (pick_succ hpd).2 x hx; rw [hterm] at this; exact this))
      exact Res.norm_eq_ok hr hga
    have hsrcG : termEval (withRegs fr' V) (memPlus m) lg.term = .ok (d.block, vs, memPlus m) := by
      rw [termEval_pick (by rw [hbr]; exact hB), hlt, hpd']
      simp only [Res.ok_bind, mapBlockCall, hgm]; rfl
    -- what the rewritten terminator does
    have hBR : effTerm (withRegs fr' V) (memPlus m) (effsL lg.extra.toList) lg.term' =
          .ok (d.block, vs, memPlus m) ∨
        ∃ c, (trapMap f).get? d.block = some c ∧
          effTerm (withRegs fr' V) (memPlus m) (effsL lg.extra.toList) lg.term' = .trap c := by
      cases hch : lg.changed
      · simp only [SimpCtx.termOk, hch, Bool.false_eq_true, if_false, Bool.and_eq_true,
          Array.isEmpty_iff, beq_iff_eq] at htok
        obtain ⟨hex, hte⟩ := htok
        left
        rw [hex, hte]
        simpa [effsL, effTerm] using hsrcG
      · have := (hfa.2 hch).1 _ _ _ hsrcG
        rw [← effsOf_eq]
        rcases this with h1 | ⟨c, hc, h2⟩
        · exact .inl h1
        · exact .inr ⟨c, hc, h2⟩
    -- the extras
    have hE : ∀ t ∈ lg.extra.toList, insOk t = true ∨
        (trapOk t = true ∧ ∀ x ∈ operands t.inst, cert.subst.step x = x) := by
      intro t ht
      cases hch : lg.changed
      · simp only [SimpCtx.termOk, hch, Bool.false_eq_true, if_false, Bool.and_eq_true,
          Array.isEmpty_iff, beq_iff_eq] at htok
        rw [htok.1] at ht; simp at ht
      · simp only [SimpCtx.termOk, hch, if_true, Bool.and_eq_true] at htok
        have := arr_all htok.2 t ht
        simp only [Bool.or_eq_true, Bool.and_eq_true] at this
        rcases this with h1 | ⟨h1, h2⟩
        · exact .inl h1
        · exact .inr ⟨h1, SimpCtx.fixed_step (c := sctx g fi cert bi) h2⟩
    have hT : mapTerm cert.subst.step lg.term' = lg.term' := by
      cases hch : lg.changed
      · simp only [SimpCtx.termOk, hch, Bool.false_eq_true, if_false, Bool.and_eq_true,
          Array.isEmpty_iff, beq_iff_eq] at htok
        rw [htok.2, hlt, mapTerm_step_idem hS.chain]
      · simp only [SimpCtx.termOk, hch, if_true, Bool.and_eq_true] at htok
        conv => rhs; rw [← mapTerm_id lg.term']
        exact mapTerm_congr (SimpCtx.fixed_step (c := sctx g fi cert bi) htok.1.2)
    rw [← hVd] at hV hBR
    simp only [VAt] at hV hBR
    rcases h.toSCore.runExtras hS hm (fr0 := fr') (ρ := rhoAt f g fi cert fr' bi k') lg.term'
        lg.extra.toList hbody (fun t ht => hE t ht) rfl rfl hV with
      ⟨fr2, K2, hst, hb2, h3, hf2, hs2, ht2, hV2, he2⟩ | ⟨fr2, c, hst, htr2, he2⟩
    · have hT2 : fr2.term = lg.term' := by rw [ht2, ht', hT]
      rw [he2] at hBR
      rcases hBR with hok | ⟨c, hc, htr⟩
      · -- the same branch
        have hB2 : isBranch lg.term' = true := termEval_isBranch hok
        rw [termEval_pick hB2] at hok
        simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at hok
        obtain ⟨d2, hp2, vs2, hg2, hdb, rfl, -⟩ := hok
        obtain ⟨b2', hb2', h2b, -, hK2⟩ := h3.invg.block
        rw [hb'] at hb2'; cases hb2'
        have hK2' : K2 = b'.body.length := by
          rw [hb2] at h2b; have := List.drop_eq_nil_iff.1 h2b.symm; omega
        have hagr : ∀ x ∈ termOperands lg.term', fr2.regs x =
            (withRegs fr' (den cert.graph (rhoAt f g fi cert fr' bi k') fr' (memPlus m))).regs x := by
          intro x hx
          have := hS.wfg.termUses bi b' hb' x (by
            obtain ⟨b0, hb0, -, ht0, -⟩ := h3.invg.block
            rw [hb'] at hb0; cases hb0
            rw [← ht0, hT2]; exact hx)
          rw [← hK2'] at this
          exact (hV2 x this).symm
        have hp2' : pick fr2 fr2.term = .ok d2 := by rw [hT2, pick_congr hagr]; exact hp2
        have hg2' : fr2.getMany d2.args = .ok vs2 := by
          rw [getMany_congr (fun x hx => hagr x ((pick_succ hp2).2 x hx))]; exact hg2
        obtain ⟨fr1', he1', j, hr1⟩ := h3.enter hS hs hb2 (pick_succ hpd).1
          he (by rw [hT2]; exact (pick_succ hp2).1) hdb hga hg2'
        refine ⟨fr1', hst.trans (.single ?_), .inl ⟨j, 0, 0, hr1⟩⟩
        rw [lstep_pick hb2 (by rw [hT2]; exact hB2), hp2']
        simp only [LRes.ofRes, he1']
      · -- a trap block
        have hTt := termEval_trapc htr
        obtain ⟨blk0, hm0, hid0, htb⟩ := trapMap_spec hc
        have hbl : blk0 = blk := block_unique hS.wff hm0 hid0 (by rw [← h.invf.func]; exact hblk)
        subst hbl
        obtain ⟨hbt, hbp⟩ := trapBlock?_spec htb
        refine ⟨fr2, hst, .inr ⟨c, h.invf.func, by rw [hf2, h.invg.func], by
          rw [hs2, h.slots], hbt, hbp, fun m' => ?_⟩⟩
        rw [lstep_term hb2, hT2, hTt]
    · rcases hBR with hok | ⟨c', hc, htr⟩
      · rw [he2] at hok; cases hok
      · rw [he2] at htr; cases htr
        obtain ⟨blk0, hm0, hid0, htb⟩ := trapMap_spec hc
        have hbl : blk0 = blk := block_unique hS.wff hm0 hid0 (by rw [← h.invf.func]; exact hblk)
        subst hbl
        obtain ⟨hbt, hbp⟩ := trapBlock?_spec htb
        have hsl2 : fr2.slots = fr'.slots := (LStar.frame hst).2.1
        have hf2 : fr2.func = fr'.func := (LStar.frame hst).1
        exact ⟨fr2, hst, .inr ⟨c, h.invf.func, by rw [hf2, h.invg.func], by
          rw [hsl2, h.slots], hbt, hbp, htr2⟩⟩
  · -- not a branch: the terminator is kept
    have hch : lg.changed = false := by
      cases hc : lg.changed
      · rfl
      · simp only [SimpCtx.termOk, hc, if_true, Bool.and_eq_true] at htok
        rw [hbr] at htok; exact absurd htok.1.1 hB
    simp only [SimpCtx.termOk, hch, Bool.false_eq_true, if_false, Bool.and_eq_true,
      Array.isEmpty_iff, beq_iff_eq] at htok
    obtain ⟨hex, hte⟩ := htok
    have ht0 : fr'.body = [] := by rw [hbody, hex]; rfl
    have hterm' : fr'.term = mapTerm cert.subst.step fr.term := by
      rw [ht', hte, hlt, mapTerm_step_idem hS.chain, hterm]
    rw [lstep_term hs]
    cases hTT : fr.term with
    | ret xs =>
      rw [hTT] at hops
      have hlt' : lstep fr' m = LRes.ofRes (fr'.getMany (xs.map cert.subst.step))
          fun vals => .ret vals := by
        rw [lstep_term ht0, hterm', hTT]; rfl
      have hg := getMany_rename (fr := fr) (fr' := fr') (σ := cert.subst.step) (xs := xs)
        (fun x hx => hops x hx)
      simp only
      refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_, fun vals hl => ⟨fr', .refl _ _, ?_⟩,
        fun _ _ hl => ?_⟩
      all_goals cases hc : fr.getMany xs with
        | trap c'' => exact absurd hc (getMany_not_trap _ _ _)
        | stuck _ => rw [hc] at hl; cases hl
        | ok vs =>
          rw [hc] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.ret.injEq] at hl; subst hl; rw [hlt', Res.norm_eq_ok hg hc]; rfl)
    | returnCall fn args =>
      rw [hTT] at hops
      have hlt' : lstep fr' m = LRes.ofRes (tailArgs fr' fn (args.map cert.subst.step))
          fun (ext, vals) => .tail ext vals := by
        rw [lstep_term ht0, hterm', hTT]; rfl
      have hg := tailArgs_rename (fr := fr) (fr' := fr') (σ := cert.subst.step) (fn := fn)
        (args := args) (by rw [h.invf.func, h.invg.func, hS.externs])
        (by rw [h.invf.func, h.invg.func, hS.sig]) (fun x hx => hops x hx)
      simp only
      refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_, fun vals hl => ?_,
        fun ext vals hl => ⟨fr', .refl _ _, ?_⟩⟩
      all_goals cases hc : tailArgs fr fn args with
        | trap c'' =>
          rw [hc] at hl
          first
          | (cases hl; done)
          | (cases hl; exact ⟨fr', m, .refl _ _, by rw [hlt', Res.norm_eq_trap hg hc]; rfl⟩)
        | stuck _ => rw [hc] at hl; cases hl
        | ok p =>
          obtain ⟨e, vs⟩ := p
          rw [hc] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.tail.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
             rw [hlt', Res.norm_eq_ok hg hc]; rfl)
    | trap c =>
      have hlt' : lstep fr' m = .trap c := by rw [lstep_term ht0, hterm', hTT]; rfl
      exact ⟨fun _ _ hl => by simp at hl, fun c' hl => ⟨fr', m, .refl _ _, by rw [hlt']; simpa using hl⟩,
        fun _ hl => by simp at hl, fun _ _ hl => by simp at hl⟩
    | jump _ => rw [hterm] at hTT; rw [hTT] at hB; simp [isBranch] at hB
    | brif _ _ _ => rw [hterm] at hTT; rw [hTT] at hB; simp [isBranch] at hB
    | brTable _ _ _ => rw [hterm] at hTT; rw [hTT] at hB; simp [isBranch] at hB
end

/-! ## The simulation -/

/-- A pure statement steps without touching memory. -/
theorem lstep_pure {fr fr1 : Frame} {m m1 : Mem} {s : Stmt} {ss : List Stmt}
    (hs : fr.body = s :: ss) (hp : isPure s.inst = true) (h : lstep fr m = .next fr1 m1) :
    m1 = m ∧ fr1.func = fr.func ∧ fr1.slots = fr.slots ∧ fr1.term = fr.term ∧ fr1.body = ss := by
  have hnc : ∀ fn args, s.inst ≠ .call fn args := by
    intro fn args he; rw [he] at hp; cases hp
  rw [lstep_inst hs hnc] at h
  cases he : evalInst fr m s.inst with
  | ok p =>
    obtain ⟨vals, m'⟩ := p
    rw [he] at h; simp only [LRes.ofRes] at h
    split at h
    · cases h; exact ⟨(evalInst_pure hp he).1, rfl, rfl, rfl, rfl⟩
    · cases h
  | trap _ => rw [he] at h; cases h
  | stuck _ => rw [he] at h; cases h

theorem lstep_pure_ne_trap {fr : Frame} {m : Mem} {s : Stmt} {ss : List Stmt}
    (hs : fr.body = s :: ss) (hp : isPure s.inst = true) (c : TrapCode) : lstep fr m ≠ .trap c := by
  have hnc : ∀ fn args, s.inst ≠ .call fn args := by
    intro fn args he; rw [he] at hp; cases hp
  intro h
  rw [lstep_inst hs hnc] at h
  cases he : evalInst fr m s.inst with
  | ok p =>
    obtain ⟨_, _⟩ := p
    rw [he] at h; simp only [LRes.ofRes] at h; split at h <;> cases h
  | trap c' => exact (evalInst_removable (by simp [removable, hp])).2 c' he
  | stuck _ => rw [he] at h; cases h

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  (hF : SimpFacts f fi cert) {syms : String → Option Nat}
include hS hF

/-- `SSR` is a simulation. -/
theorem SSR.isSim : IsSim syms (SSR f g fi cert syms) where
  frame := by
    rintro fr fr' (⟨bi, k, k', h⟩ | ⟨c, hf, hg, hsl, -⟩)
    · exact ⟨h.slots, by rw [h.invg.func, h.invf.func, hS.sig]⟩
    · exact ⟨hsl, by rw [hg, hf, hS.sig]⟩
  next := by
    rintro fr fr' m fr1 m1 (⟨bi, k, k', h⟩ | ⟨c, hf, hg, hsl, ht, hp, htr⟩) hm hl
    · cases hs : fr.body with
      | nil => exact (h.term hS hF hm hs).1 fr1 m1 hl
      | cons s ss =>
        obtain ⟨fr1', hst, k1, h1⟩ := (h.stmt hS hF hm hs).1 fr1 m1 hl
        exact ⟨fr1', hst, .inl ⟨bi, k + 1, k1, h1⟩⟩
    · cases hs : fr.body with
      | nil => rw [lstep_term hs, ht] at hl; cases hl
      | cons s ss =>
        obtain ⟨rfl, hf1, hs1, ht1, hb1⟩ := lstep_pure hs (hp s (by simp [hs])) hl
        exact ⟨fr', .refl _ _, .inr ⟨c, by rw [hf1, hf], hg, by rw [hs1, hsl], by rw [ht1, ht],
          fun s' hs' => hp s' (by rw [hs, ← hb1]; exact List.mem_cons_of_mem _ hs'), htr⟩⟩
  call := by
    rintro fr fr' m ext vals rs rest (⟨bi, k, k', h⟩ | ⟨c, hf, hg, hsl, ht, hp, htr⟩) hm hl
    · obtain ⟨st, fn, args, hb, -, -, -⟩ := lstep_call_inv hl
      obtain ⟨fr2, rs', rest', hst, hl', hcont⟩ := (h.stmt hS hF hm hb).2.2 ext vals rs rest hl
      exact ⟨fr2, rs', rest', hst, hl', Cont.mono (fun a b ⟨k1, hab⟩ => .inl ⟨bi, k + 1, k1, hab⟩)
        hcont⟩
    · obtain ⟨st, fn, args, hb, hc, -, -⟩ := lstep_call_inv hl
      have := hp st (by simp [hb])
      rw [hc] at this; cases this
  ret := by
    rintro fr fr' m vals (⟨bi, k, k', h⟩ | ⟨c, hf, hg, hsl, ht, hp, htr⟩) hm hl
    · exact (h.term hS hF hm (lstep_ret_inv hl)).2.2.1 vals hl
    · rw [lstep_term (lstep_ret_inv hl), ht] at hl; cases hl
  tail := by
    rintro fr fr' m ext vals (⟨bi, k, k', h⟩ | ⟨c, hf, hg, hsl, ht, hp, htr⟩) hm hl
    · exact (h.term hS hF hm (lstep_tail_inv hl)).2.2.2 ext vals hl
    · rw [lstep_term (lstep_tail_inv hl), ht] at hl; cases hl
  trap := by
    rintro fr fr' m c (⟨bi, k, k', h⟩ | ⟨c0, hf, hg, hsl, ht, hp, htr⟩) hm hl
    · cases hs : fr.body with
      | nil => exact (h.term hS hF hm hs).2.1 c hl
      | cons s ss => exact (h.stmt hS hF hm hs).2.1 c hl
    · cases hs : fr.body with
      | nil =>
        rw [lstep_term hs, ht] at hl; cases hl
        exact ⟨fr', m, .refl _ _, htr m⟩
      | cons s ss => exact absurd hl (lstep_pure_ne_trap hs (hp s (by simp [hs])) c)

end

/-- **The simplify validator is sound**: `simpOk f g fi cert` and the facts of the run
(`SimpFacts`, `FV/Opt/Proof/SimpLoop.lean`) give `FunSim f g`. -/
theorem simpOk_sim {f g : Function} {fi : Info} {cert : SimpCert} (hf : check f = .ok fi)
    (h : simpOk f g fi cert = true) (hF : SimpFacts f fi cert) : FunSim f g := by
  have hS := simpOk_facts hf h
  refine ⟨hS.name, hS.sig, hS.slots, fun syms => ⟨_, SSR.isSim hS hF, fun b hb => ?_⟩⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  obtain ⟨b', lg, hb0', -, -, hpar, -, -, -, -, -, hps, -⟩ := hS.blocks 0 b hb0
  refine ⟨b', by simpa [Function.entry?, List.head?_eq_getElem?] using hb0', hpar,
    fun args regs slots hty hr hsl => .inl ⟨0, 0, 0, ⟨⟨Inv.entry hS.wff hb hty hr hsl, ?_, ?_, rfl⟩,
      fun lg hlg => by simp [outs]⟩⟩⟩
  · rw [← hpar] at hty hr
    exact Inv.entry hS.wfg (by simpa [Function.entry?, List.head?_eq_getElem?] using hb0') hty hr
      (by rw [hsl, hS.slots])
  · intro v hv
    have hd := avail_entry hS.wff hv
    obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hS.wff hd
    rw [hb0] at hb1; cases hb1
    have hσv : cert.subst.step v = v := by rw [← hpv]; exact step_of_not_contains (hps p hp).2.2
    have hgs : (wfData g (gInfo fi cert)).dm v = some (0, 0) := by
      rw [← hpv]; exact site_param hS.wfg hb0' (by rw [hpar]; exact hp)
    rw [hσv]
    refine ⟨⟨0, 0, hgs, .inl ⟨rfl, Nat.le_refl _⟩⟩, rfl, ?_⟩
    intro d t hdt
    rw [hd] at hdt; simp only [Option.some.injEq, Prod.mk.injEq] at hdt
    obtain ⟨rfl, -⟩ := hdt
    exact ⟨0, 0, by rw [hσv]; exact hgs, .refl _⟩

end Opt
