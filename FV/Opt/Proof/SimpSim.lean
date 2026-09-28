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

end Opt
