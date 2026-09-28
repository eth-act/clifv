import FV.Opt.Proof.SimpMat
import FV.Opt.Proof.SimpFacts
import FV.Opt.Proof.SimpSim

/-!
# The loop invariant of the simplify pass: every run has its facts (`Opt.simplify_facts`)

For sound rule sets (`Opt.SimplifySound`, `Opt.SkeletonSound`) and a checked input, every run of
`Opt.simplify` has the semantic facts `Opt.SimpFacts` its certificate records. Fix a good
environment (`SGood`: a valuation `ρ` of the leaves, a frame, a memory defining every symbol);
the pass state keeps the graph invariant `GInv` (`FV/Opt/Proof/SimpGraph.lean`), and

* each record's fact holds in the graph valuation `gval` of the state right after the record
  was made: a replacement `w` of `v = n` has `n`'s value (`optimizeAt_spec`, the hash-consing
  table, `materialize_spec`); a skeleton outcome refines the statement (`runSkel_spec`,
  composed along the chain `skelStmt`/`skelTerm` took, through the renamings of
  `materializeAll`);
* every value a fact mentions is *known* then, and the valuation of known values never changes
  afterwards (`Mono`: the graph only grows by fresh values, and materialisation keeps values),
  so the facts hold in the final valuation, which is `den` of the certificate's graph.
-/

namespace Opt

open Clif

/-! ## The valuation only grows -/

section
variable {ρ : Valuation} {fr : Frame} {mem : Mem}

/-- How the state changes along the pass: known values stay known with the same value. -/
structure Mono (ρ : Valuation) (fr : Frame) (mem : Mem) (st st' : SState) : Prop where
  known : ∀ x, st.known x = true → st'.known x = true
  fix : ∀ x, st.known x = true → gval ρ fr mem st' x = gval ρ fr mem st x
  trap : st'.trapBlocks = st.trapBlocks
  fn : st'.fn = st.fn

theorem Mono.refl (st : SState) : Mono ρ fr mem st st := ⟨fun _ h => h, fun _ _ => rfl, rfl, rfl⟩

theorem Mono.trans {st1 st2 st3 : SState} (h1 : Mono ρ fr mem st1 st2) (h2 : Mono ρ fr mem st2 st3) :
    Mono ρ fr mem st1 st3 :=
  ⟨fun x h => h2.known x (h1.known x h), fun x h => (h2.fix x (h1.known x h)).trans (h1.fix x h),
   h2.trap.trans h1.trap, h2.fn.trans h1.fn⟩

theorem Grow.mono {st st' : SState} (h : Grow ρ fr mem st st') : Mono ρ fr mem st st' :=
  ⟨h.known, h.fix, h.trap, h.fn⟩

theorem MGrow.mono {st st' : SState} (h : MGrow ρ fr mem st st') : Mono ρ fr mem st st' :=
  ⟨h.known, h.fix, h.trap, h.fn⟩

/-- Same graph and known values. -/
theorem Mono.of_graph {st st' : SState} (hd : st'.defs = st.defs)
    (ha : ∀ x, st.avail.contains x = true → st'.avail.contains x = true)
    (ht : st'.trapBlocks = st.trapBlocks) (hf : st'.fn = st.fn) : Mono ρ fr mem st st' := by
  have hgr : st'.graph = st.graph := by funext x; simp [SState.graph, hd]
  refine ⟨fun x hx => ?_, fun x _ => by simp only [gval, hgr], ht, hf⟩
  simp only [SState.known, Bool.or_eq_true] at hx ⊢
  rcases hx with hx | hx
  · exact .inl (by rw [hd]; exact hx)
  · exact .inr (ha x hx)

end

/-! ## Facts persist as the valuation grows -/

theorem evalInst_V_eq {fr : Frame} {M : Mem} {V V' : Valuation} {i : Inst}
    (h : ∀ x ∈ operands i, V' x = V x) : evalInst (withRegs fr V') M i = evalInst (withRegs fr V) M i :=
  evalInst_congr rfl rfl h


/-- A result that is not `stuck` (an evaluation that read all it needed). -/
def NotStuck {α : Type} (r : Res α) : Prop := ∀ m, r ≠ .stuck m

section
variable {fr : Frame} {mem : Mem} {V V' : Valuation} (hle : Valuation.Le V V')
include hle

theorem evalInst_grow {M : Mem} {i : Inst} (h : NotStuck (evalInst (withRegs fr V) M i)) :
    evalInst (withRegs fr V') M i = evalInst (withRegs fr V) M i :=
  evalInst_mono (fr := withRegs fr V) (fr' := withRegs fr V') rfl rfl hle h

theorem get_grow {x : ValueId} (h : NotStuck ((withRegs fr V).get x)) :
    (withRegs fr V').get x = (withRegs fr V).get x := by
  simp only [Frame.get, withRegs] at h ⊢
  cases hx : V x with
  | some a => rw [hle x a hx]
  | none => rw [hx] at h; exact absurd rfl (h _)

theorem getMany_grow : ∀ {xs : List ValueId}, NotStuck ((withRegs fr V).getMany xs) →
    (withRegs fr V').getMany xs = (withRegs fr V).getMany xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [Frame.getMany] at h ⊢
    have hx : NotStuck ((withRegs fr V).get x) := by
      intro m hm; rw [hm] at h; exact h m rfl
    rw [get_grow hle hx]
    cases hg : (withRegs fr V).get x with
    | ok a =>
      simp only [Res.ok_bind] at h ⊢
      have hxs : NotStuck ((withRegs fr V).getMany xs) := by
        intro m hm; rw [hg, Res.ok_bind, hm] at h; exact h m rfl
      rw [getMany_grow hxs]
    | _ => rfl

theorem seqEval2_grow {M : Mem} {a b : Inst} (h : NotStuck (seqEval2 (withRegs fr V) M a b)) :
    seqEval2 (withRegs fr V') M a b = seqEval2 (withRegs fr V) M a b := by
  simp only [seqEval2] at h ⊢
  have ha : NotStuck (evalInst (withRegs fr V) M a) := by
    intro m hm; rw [hm] at h; exact h m rfl
  rw [evalInst_grow hle ha]
  split
  · rename_i m' hm
    rw [hm] at h
    exact evalInst_grow hle h
  · rfl
  · rfl
  · rfl

theorem termEval_grow {M : Mem} {t : Terminator} (h : NotStuck (termEval (withRegs fr V) M t)) :
    termEval (withRegs fr V') M t = termEval (withRegs fr V) M t := by
  cases t with
  | jump d =>
    simp only [termEval] at h ⊢
    have hg : NotStuck ((withRegs fr V).getMany d.args) := by
      intro m hm; rw [hm] at h; exact h m rfl
    rw [getMany_grow hle hg]
  | brif c th el =>
    simp only [termEval] at h ⊢
    have hc : NotStuck ((withRegs fr V).get c) := by
      intro m hm; rw [hm] at h; exact h m rfl
    rw [get_grow hle hc]
    cases hg : (withRegs fr V).get c with
    | ok cv =>
      rw [hg] at h; simp only [Res.ok_bind] at h ⊢
      have hm' : NotStuck ((withRegs fr V).getMany (if Sem.truthy cv.bits then th else el).args) := by
        intro m hm; rw [hm] at h; exact h m rfl
      rw [getMany_grow hle hm']
    | _ => rfl
  | brTable x d tbl =>
    simp only [termEval] at h ⊢
    have hc : NotStuck ((withRegs fr V).get x) := by
      intro m hm; rw [hm] at h; exact h m rfl
    rw [get_grow hle hc]
    cases hg : (withRegs fr V).get x with
    | ok xv =>
      rw [hg] at h; simp only [Res.ok_bind] at h ⊢
      have hm' : NotStuck ((withRegs fr V).getMany (tbl[xv.toNat]?.getD d).args) := by
        intro m hm; rw [hm] at h; exact h m rfl
      rw [getMany_grow hle hm']
    | _ => rfl
  | ret _ => rfl
  | returnCall _ _ => rfl
  | trap _ => rfl

theorem effTerm_grow {t : Terminator} : ∀ {E : List Inst} {M : Mem},
    NotStuck (effTerm (withRegs fr V) M E t) →
    effTerm (withRegs fr V') M E t = effTerm (withRegs fr V) M E t
  | [], M, h => by simp only [effTerm] at h ⊢; exact termEval_grow hle h
  | a :: E, M, h => by
    simp only [effTerm] at h ⊢
    have ha : NotStuck (evalInst (withRegs fr V) M a) := by
      intro m hm; rw [hm] at h; exact h m rfl
    rw [evalInst_grow hle ha]
    split
    · rename_i m' hm
      rw [hm] at h
      exact effTerm_grow h
    all_goals rfl

end

theorem ResRefines.grow {α : Type} {A A' B B' : Res α} (h : ResRefines A B) (hA : A' = A)
    (hB : NotStuck B → B'.norm = B.norm) : ResRefines A' B' := by
  subst hA
  refine ⟨fun x hx => ?_, fun c hc => ?_⟩
  · have := h.1 x hx; exact Res.norm_eq_ok (hB (by rw [this]; intro m hm; cases hm)) this
  · have := h.2 c hc; exact Res.norm_eq_trap (hB (by rw [this]; intro m hm; cases hm)) this

theorem BrRefines.grow {tb : BlockId → Option TrapCode} {A A' B B' : Res (BlockId × List Val × Mem)}
    (h : BrRefines tb A B) (hA : A' = A) (hB : NotStuck B → B'.norm = B.norm) :
    BrRefines tb A' B' := by
  subst hA
  refine ⟨fun bid vs m hx => ?_, fun c hc => ?_⟩
  · rcases h.1 bid vs m hx with h1 | ⟨c, hc, h2⟩
    · exact .inl (Res.norm_eq_ok (hB (by rw [h1]; intro m hm; cases hm)) h1)
    · exact .inr ⟨c, hc, Res.norm_eq_trap (hB (by rw [h2]; intro m hm; cases hm)) h2⟩
  · have := h.2 c hc; exact Res.norm_eq_trap (hB (by rw [this]; intro m hm; cases hm)) this

/-- The source instruction of a record (its operands are known when the record is made). -/
def StmtLog.srcOps : StmtLog → List ValueId
  | .keep _ => []
  | .repl s' _ _ => operands s'.inst
  | .skel s' _ _ => operands s'.inst

section
variable {fr : Frame} {mem : Mem} {V V' : Valuation}

theorem SkelFact.grow (hle : Valuation.Le V V') {i : Inst} {o : SkelOut}
    (hsrc : ∀ x ∈ operands i, V' x = V x) (hf : SkelFact (withRegs fr V) mem V i o) :
    SkelFact (withRegs fr V') mem V' i o := by
  have hi : evalInst (withRegs fr V') mem i = evalInst (withRegs fr V) mem i :=
    evalInst_V_eq hsrc
  cases o with
  | keep => trivial
  | remove => simpa only [SkelFact, hi] using hf
  | removeWithVal v =>
    simp only [SkelFact, hi] at hf ⊢
    refine ⟨fun vs m he => ?_, hf.2⟩
    obtain ⟨h1, a, h2, h3⟩ := hf.1 vs m he
    exact ⟨h1, a, h2, hle v a h3⟩
  | replace i' => exact ResRefines.grow hf hi (fun h => by rw [evalInst_grow hle h])
  | two a b => exact ResRefines.grow hf hi (fun h => by rw [seqEval2_grow hle h])

theorem LogFact.grow (hle : Valuation.Le V V') {l : StmtLog}
    (hsrc : ∀ x ∈ l.srcOps, V' x = V x) (hf : LogFact (withRegs fr V) mem V l) :
    LogFact (withRegs fr V') mem V' l := by
  cases l with
  | keep => trivial
  | repl s' w out =>
    intro a ha
    rw [evalNode_congr (fr := withRegs fr V) (fr' := withRegs fr V') rfl rfl hsrc] at ha
    exact hle w a (hf a ha)
  | skel s' o out => exact SkelFact.grow hle hsrc hf

theorem TermFact.grow (hle : Valuation.Le V V') {tb : BlockId → Option TrapCode} {lg : BlockLog}
    (hsrc : ∀ x ∈ termOperands lg.term, V' x = V x)
    (hf : lg.changed = true →
      BrRefines tb (termEval (withRegs fr V) mem lg.term) (effTerm (withRegs fr V) mem (effsOf lg.extra) lg.term')) :
    lg.changed = true →
      BrRefines tb (termEval (withRegs fr V') mem lg.term) (effTerm (withRegs fr V') mem (effsOf lg.extra) lg.term') :=
  fun hc => BrRefines.grow (hf hc) (termEval_congr (fr := withRegs fr V) (fr' := withRegs fr V') hsrc)
    (fun h => by rw [effTerm_grow hle h])

end

/-! ## Composition of refinements -/

theorem ResRefines.trans {α : Type} {a b c : Res α} (h1 : ResRefines a b) (h2 : ResRefines b c) :
    ResRefines a c :=
  ⟨fun x hx => h2.1 x (h1.1 x hx), fun t ht => h2.2 t (h1.2 t ht)⟩

theorem ResRefines.of_norm {α : Type} {a b a' b' : Res α} (h : ResRefines a b)
    (ha : a'.norm = a.norm) (hb : b'.norm = b.norm) : ResRefines a' b' :=
  ⟨fun x hx => Res.norm_eq_ok hb (h.1 x (Res.norm_eq_ok ha.symm hx)),
   fun t ht => Res.norm_eq_trap hb (h.2 t (Res.norm_eq_trap ha.symm ht))⟩

theorem BrRefines.trans {tb : BlockId → Option TrapCode} {a b c : Res (BlockId × List Val × Mem)}
    (h1 : BrRefines tb a b) (h2 : BrRefines tb b c) : BrRefines tb a c := by
  refine ⟨fun bid vs m ha => ?_, fun t ht => h2.2 t (h1.2 t ht)⟩
  rcases h1.1 bid vs m ha with hb | ⟨c', hc', hb⟩
  · exact h2.1 bid vs m hb
  · exact .inr ⟨c', hc', h2.2 c' hb⟩

theorem BrRefines.of_norm {tb : BlockId → Option TrapCode} {a b a' b' : Res (BlockId × List Val × Mem)}
    (h : BrRefines tb a b) (ha : a'.norm = a.norm) (hb : b'.norm = b.norm) : BrRefines tb a' b' := by
  refine ⟨fun bid vs m hx => ?_, fun t ht => Res.norm_eq_trap hb (h.2 t (Res.norm_eq_trap ha.symm ht))⟩
  rcases h.1 bid vs m (Res.norm_eq_ok ha.symm hx) with h1 | ⟨c, hc, h2⟩
  · exact .inl (Res.norm_eq_ok hb h1)
  · exact .inr ⟨c, hc, Res.norm_eq_trap hb h2⟩

/-- A refinement step followed by a skeleton outcome of the replacement. -/
theorem SkelFact.pre {fr : Frame} {mem : Mem} {V : Valuation} {i i' : Inst} {o : SkelOut}
    (h1 : ResRefines (evalInst fr mem i) (evalInst fr mem i')) (h2 : SkelFact fr mem V i' o)
    (ho : ∀ j, o ≠ .replace j → True := fun _ _ => trivial) :
    SkelFact fr mem V i (o.orReplace i') := by
  cases o with
  | keep => exact h1
  | remove =>
    exact ⟨fun vs m he => h2.1 vs m (h1.1 _ he), fun c he => h2.2 c (h1.2 c he)⟩
  | removeWithVal v =>
    exact ⟨fun vs m he => h2.1 vs m (h1.1 _ he), fun c he => h2.2 c (h1.2 c he)⟩
  | replace j => exact h1.trans h2
  | two a b => exact h1.trans h2

/-! ## Renaming by materialised values -/

theorem seqEval2_rename {σ : ValueId → ValueId} {F F' : Frame} {M : Mem} {a b : Inst}
    (hg : F'.func.globals = F.func.globals) (hs : F'.slots = F.slots)
    (h : ∀ x ∈ operands a ++ operands b, F'.regs (σ x) = F.regs x) :
    (seqEval2 F' M (mapOperands σ a) (mapOperands σ b)).norm = (seqEval2 F M a b).norm := by
  have ha := evalInst_rename (mem := M) hg hs (fun x hx => h x (List.mem_append_left _ hx))
  simp only [seqEval2]
  cases he : evalInst F M a with
  | ok p =>
    obtain ⟨vs, m⟩ := p
    rw [Res.norm_eq_ok ha he]
    cases vs with
    | nil => exact evalInst_rename hg hs (fun x hx => h x (List.mem_append_right _ hx))
    | cons _ _ => rfl
  | trap c => rw [Res.norm_eq_trap ha he]
  | stuck msg =>
    rw [he] at ha
    cases he' : evalInst F' M (mapOperands σ a) <;> rw [he'] at ha <;> simp_all [Res.norm]

section Skel
variable {f : Function} {ρ : Valuation} {fr : Frame} {mem : Mem}
  {rules : SimplifyFn} {skel : SkeletonFn} {allowed skelOk : Inst → Bool} {cfg : Cfg} {bi : Nat}

theorem gval_le {st st' : SState} (h : GInv f ρ fr mem st) (hm : Mono ρ fr mem st st') :
    Valuation.Le (gval ρ fr mem st) (gval ρ fr mem st') := by
  intro x a hx
  rw [hm.fix x (known_of_gval h hx)]; exact hx

/-- An instruction whose operands were materialised (`materializeAll`, renaming `m`) evaluates,
when it does not get stuck, as before the renaming. -/
theorem renamed_eval {st1 st2 st3 : SState} {m : List (ValueId × ValueId)} {i : Inst} {M : Mem}
    (h1 : GInv f ρ fr mem st1) (h2 : GInv f ρ fr mem st2) (hm12 : Mono ρ fr mem st1 st2)
    (hm23 : Mono ρ fr mem st2 st3)
    (hren : ∀ y ∈ operands i, gval ρ fr mem st2 (rename m y) = gval ρ fr mem st2 y)
    (hns : NotStuck (evalInst (withRegs fr (gval ρ fr mem st1)) M i)) :
    (evalInst (withRegs fr (gval ρ fr mem st3)) M (mapOperands (rename m) i)).norm =
      (evalInst (withRegs fr (gval ρ fr mem st1)) M i).norm := by
  have e12 := evalInst_grow (gval_le h1 hm12) hns
  have hr := evalInst_rename (σ := rename m) (fr := withRegs fr (gval ρ fr mem st2))
    (fr' := withRegs fr (gval ρ fr mem st2)) (mem := M) rfl rfl hren
  have hns2 : NotStuck (evalInst (withRegs fr (gval ρ fr mem st2)) M (mapOperands (rename m) i)) := by
    intro msg hmsg
    rw [hmsg, e12] at hr
    cases hc : evalInst (withRegs fr (gval ρ fr mem st1)) M i with
    | stuck msg' => exact hns msg' hc
    | ok _ => rw [hc] at hr; cases hr
    | trap _ => rw [hc] at hr; cases hr
  rw [evalInst_grow (gval_le h2 hm23) hns2, hr, e12]

/-- The replacement step of `skelStmt`: materialise the operands of `i`, reprocess. -/
theorem replace_case {st st1 st2 st3 : SState} {s : Stmt} {i : Inst} {m : List (ValueId × ValueId)}
    {out2 : Array Stmt} {o3 : SkelOut}
    (hE : GoodEnv f fr mem) (hI : GInv f ρ fr mem st) (hk : ∀ y ∈ operands s.inst, st.known y = true)
    (hI1 : GInv f ρ fr mem st1) (hM1 : Mono ρ fr mem st st1)
    (hR : ResRefines (evalInst (withRegs fr (gval ρ fr mem st1)) mem s.inst)
      (evalInst (withRegs fr (gval ρ fr mem st1)) mem i))
    (hmat : materializeAll cfg allowed bi st1 (operands i) = some (m, st2, out2))
    (ih : GInv f ρ fr mem st2 → (∀ y ∈ operands (mapOperands (rename m) i), st2.known y = true) →
      GInv f ρ fr mem st3 ∧ Mono ρ fr mem st2 st3 ∧
        SkelFact (withRegs fr (gval ρ fr mem st3)) mem (gval ρ fr mem st3) (mapOperands (rename m) i) o3) :
    GInv f ρ fr mem st3 ∧ Mono ρ fr mem st st3 ∧
      SkelFact (withRegs fr (gval ρ fr mem st3)) mem (gval ρ fr mem st3) s.inst
        (o3.orReplace (mapOperands (rename m) i)) := by
  obtain ⟨hI2, hG2, hmap, hps⟩ := materializeAll_spec hE hI1 hmat
  have hren := rename_spec hmap hps
  have hM2 : Mono ρ fr mem st1 st2 := hG2.mono
  obtain ⟨hI3, hM3, hF3⟩ := ih hI2 (by
    intro y hy
    rw [operands_mapOperands] at hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
    exact known_of_avail (hren y0 hy0).2)
  refine ⟨hI3, hM1.trans (hM2.trans hM3), SkelFact.pre ?_ hF3⟩
  refine ResRefines.grow hR ?_ (fun hns => renamed_eval hI1 hI2 hM2 hM3 (fun y hy => (hren y hy).1) hns)
  exact evalInst_V_eq (fun x hx => ((hM2.trans hM3).fix x (hM1.known x (hk x hx))).trans
    (hM1.fix x (hk x hx)) |>.trans (hM1.fix x (hk x hx)).symm)

theorem skelStmt_spec (hS : SimplifySound rules) (hK : SkeletonSound skel) (hE : GoodEnv f fr mem) :
    ∀ fuel st s out sub st' o, GInv f ρ fr mem st → (∀ y ∈ operands s.inst, st.known y = true) →
      skelStmt skel rules allowed skelOk cfg bi fuel st s = (out, sub, st', o) →
      GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' ∧
        SkelFact (withRegs fr (gval ρ fr mem st')) mem (gval ρ fr mem st') s.inst o := by
  intro fuel
  induction fuel with
  | zero =>
    intro st s out sub st' o hI _ h
    simp only [skelStmt, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, rfl⟩ := h
    exact ⟨hI, Mono.refl _, trivial⟩
  | succ fuel ih =>
    intro st s out sub st' o hI hk h
    obtain ⟨hI1, hG1, hC1⟩ := runSkel_spec (allowed := allowed) hS hK hE hI (.inst s.inst)
    rw [skelStmt] at h
    generalize runSkel skel rules allowed st (.inst s.inst) = r at h hI1 hG1 hC1
    obtain ⟨c, st1⟩ := r
    simp only at h hI1 hG1 hC1
    have hM1 : Mono ρ fr mem st st1 := hG1.mono
    have hsrc1 : ∀ x ∈ operands s.inst, gval ρ fr mem st1 x = gval ρ fr mem st x :=
      fun x hx => hM1.fix x (hk x hx)
    have hkeep : ((#[s], [], st1, SkelOut.keep) : Array Stmt × List (ValueId × ValueId) × SState × SkelOut) =
        (out, sub, st', o) → GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' ∧
          SkelFact (withRegs fr (gval ρ fr mem st')) mem (gval ρ fr mem st') s.inst o := by
      intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl, rfl⟩ := he
      exact ⟨hI1, hM1, trivial⟩
    split at h
    · exact hkeep h
    · -- remove
      split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨-, -, rfl, rfl⟩ := h
        exact ⟨hI1, hM1, hC1 _ rfl⟩
      · exact hkeep h
    · -- removeWithVal
      rename_i v
      have hR := hC1 _ rfl
      split at h
      · split at h
        · exact hkeep h
        · split at h
          · rename_i r _ _ v' st2 out2 hmat
            simp only [Prod.mk.injEq] at h
            obtain ⟨-, -, rfl, rfl⟩ := h
            have hok := materialize_spec (f := f) (cfg := cfg) (allowed := allowed) (bi := bi) hE
              _ _ _ _ _ _ _ hI1 hmat
            have hM2 : Mono ρ fr mem st1 st2 := hok.grow.mono
            refine ⟨hok.inv, hM1.trans hM2, ?_⟩
            have hev : evalInst (withRegs fr (gval ρ fr mem st2)) mem s.inst =
                evalInst (withRegs fr (gval ρ fr mem st1)) mem s.inst :=
              evalInst_V_eq (fun x hx => hM2.fix x (hM1.known x (hk x hx)))
            simp only [SkelFact, hev]
            obtain ⟨hR1, hR2⟩ := hR
            refine ⟨fun vs m he => ?_, hR2⟩
            obtain ⟨h1, a, h2, h3⟩ := hR1 vs m he
            exact ⟨h1, a, h2, by rw [hok.val]; exact h3⟩
          · exact hkeep h
      · exact hkeep h
    · -- replace
      rename_i i
      have hR := hC1 _ rfl
      split at h
      · exact hkeep h
      · split at h
        · rename_i m st2 out2 hmat
          generalize hrec : skelStmt skel rules allowed skelOk cfg bi fuel st2
            { s with inst := mapOperands (rename m) i } = rr at h
          obtain ⟨more, sub3, st3, o3⟩ := rr
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, -, rfl, rfl⟩ := h
          exact replace_case hE hI hk hI1 hM1 hR hmat
            (fun hI2 hk2 => ih st2 _ more sub3 st3 o3 hI2 hk2 hrec)
        · exact hkeep h
    · -- replaceBranchCond
      rename_i cv
      have hR := hC1 _ rfl
      cases hsi : s.inst
      case trapz y code =>
        rw [← hsi]
        simp only [hsi] at h hR
        split at h
        · rename_i m st2 out2 hmat
          generalize hrec : skelStmt skel rules allowed skelOk cfg bi fuel st2
            { s with inst := mapOperands (rename m) (Inst.trapz cv code) } = rr at h
          obtain ⟨more, sub3, st3, o3⟩ := rr
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, -, rfl, rfl⟩ := h
          exact replace_case (i := .trapz cv code) hE hI hk hI1 hM1 (by rw [hsi]; exact hR) hmat
            (fun hI2 hk2 => ih st2 _ more sub3 st3 o3 hI2 hk2 hrec)
        · exact hkeep h
      case trapnz y code =>
        rw [← hsi]
        simp only [hsi] at h hR
        split at h
        · rename_i m st2 out2 hmat
          generalize hrec : skelStmt skel rules allowed skelOk cfg bi fuel st2
            { s with inst := mapOperands (rename m) (Inst.trapnz cv code) } = rr at h
          obtain ⟨more, sub3, st3, o3⟩ := rr
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, -, rfl, rfl⟩ := h
          exact replace_case (i := .trapnz cv code) hE hI hk hI1 hM1 (by rw [hsi]; exact hR) hmat
            (fun hI2 hk2 => ih st2 _ more sub3 st3 o3 hI2 hk2 hrec)
        · exact hkeep h
      all_goals (rw [← hsi]; simp only [hsi] at h; exact hkeep h)
    · -- replaceWithTwo
      rename_i a b
      have hR := hC1 _ rfl
      split at h
      · exact hkeep h
      · split at h
        · rename_i m st2 out2 hmat
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, -, rfl, rfl⟩ := h
          obtain ⟨hI2, hG2, hmap, hps⟩ := materializeAll_spec hE hI1 hmat
          have hren := rename_spec hmap hps
          have hM2 : Mono ρ fr mem st1 st2 := hG2.mono
          refine ⟨hI2, hM1.trans hM2, ResRefines.grow hR
            (evalInst_V_eq (fun x hx => hM2.fix x (hM1.known x (hk x hx)))) (fun hns => ?_)⟩
          rw [← seqEval2_grow (gval_le hI1 hM2) hns]
          exact seqEval2_rename rfl rfl (fun x hx => (hren x hx).1)
        · exact hkeep h
    · exact hkeep h

end Skel

/-! ## Terminators -/

/-- Statements that are pure nodes. -/
def PureOut (out : Array Stmt) : Prop := ∀ t ∈ out.toList, isPure t.inst = true

section Mat
variable {cfg : Cfg} {allowed : Inst → Bool} {bi : Nat}

theorem materialize_pure : ∀ fuel st out x x' st' out', PureOut out →
    materialize cfg allowed bi fuel (st, out) x = some (x', st', out') → PureOut out' := by
  intro fuel
  induction fuel with
  | zero => intro st out x x' st' out' _ h; simp [materialize] at h
  | succ fuel ih =>
    intro st out x x' st' out' hp h
    have hclone : ∀ st out x x' st' out', PureOut out →
        materialize.clone cfg allowed bi fuel st out x = some (x', st', out') → PureOut out' := by
      intro st out x x' st' out' hp hc
      rw [materialize.clone] at hc
      split at hc
      · cases hc
      rename_i n hx
      split at hc
      · cases hc
      rename_i hchk
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hchk
      have hpn : isPure n = true := by
        have := hchk.1.2; simp only [SState.typedNode, Bool.and_eq_true] at this
        cases hh : isPure n <;> simp_all
      let I : List ValueId → SState × Array Stmt × Array ValueId → Prop := fun _ acc => PureOut acc.2.1
      split at hc
      · cases hc
      · rename_i st2 out2 ops hf
        have hI := foldlM_option_inv _ I (by
          intro pre a c c' hc0 hg
          obtain ⟨st0, out0, ops0⟩ := c
          simp only at hg
          split at hg
          · cases hg
          · rename_i y' st1 out1 hm
            cases hg
            exact ih _ _ _ _ _ _ hc0 hm) _ [] _ _ hp hf
        simp only at hc
        split at hc
        · cases hc
        split at hc
        all_goals
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨-, -, rfl⟩ := hc
          intro t ht
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact hI t ht
          · simp only [renameOps, isPure_mapOperands]; exact hpn
    rw [materialize] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h; exact hp
      · exact hclone _ _ _ _ _ _ hp h
    · exact hclone _ _ _ _ _ _ hp h

theorem materializeAll_pure {st : SState} {xs : List ValueId} {m : List (ValueId × ValueId)}
    {st' : SState} {out : Array Stmt} (h : materializeAll cfg allowed bi st xs = some (m, st', out)) :
    PureOut out := by
  unfold materializeAll at h
  let I : List ValueId → List (ValueId × ValueId) × SState × Array Stmt → Prop :=
    fun _ acc => PureOut acc.2.2
  exact foldlM_option_inv _ I (by
    intro pre a c c' hc hg
    obtain ⟨m0, st0, out0⟩ := c
    simp only [bind, Option.bind] at hg
    split at hg
    · cases hg
    · rename_i r hr
      obtain ⟨x', st1, out1⟩ := r
      simp only [pure, Option.some.injEq] at hg
      subst hg
      exact materialize_pure _ _ _ _ _ _ _ hc hr) xs [] _ _ (fun t ht => by simp at ht) h

end Mat

theorem effsOf_append (a b : Array Stmt) : effsOf (a ++ b) = effsOf a ++ effsOf b := by
  simp [effsOf, List.filterMap_append]

theorem effsOf_pure {a : Array Stmt} (h : PureOut a) : effsOf a = [] := by
  simp only [effsOf, List.filterMap_eq_nil_iff]
  intro t ht; simp [h t ht]

theorem BrRefines.refl (tb : BlockId → Option TrapCode) (A : Res (BlockId × List Val × Mem)) :
    BrRefines tb A A := ⟨fun _ _ _ h => .inl h, fun _ h => h⟩

theorem termEval_rename {σ : ValueId → ValueId} {F F' : Frame} {M : Mem} {t : Terminator}
    (h : ∀ x ∈ termOperands t, F'.regs (σ x) = F.regs x) :
    (termEval F' M (mapTerm σ t)).norm = (termEval F M t).norm := by
  have hg : ∀ x ∈ termOperands t, (F'.get (σ x)).norm = (F.get x).norm := by
    intro x hx; simp only [Frame.get, h x hx, Res.norm_ofOption]
  cases t with
  | jump d =>
    simp only [termEval, mapTerm, mapBlockCall, Res.norm_bind, Res.norm_pure]
    rw [getMany_rename (fun x hx => h x (by simp [termOperands, hx]))]
  | brif c th el =>
    simp only [termEval, mapTerm, Res.norm_bind, Res.norm_pure]
    rw [hg c (by simp [termOperands])]
    cases (F.get c).norm with
    | ok cv =>
      simp only [Res.ok_bind]
      have : (if Sem.truthy cv.bits then mapBlockCall σ th else mapBlockCall σ el) =
          mapBlockCall σ (if Sem.truthy cv.bits then th else el) := by split <;> rfl
      rw [this]
      simp only [mapBlockCall]
      rw [getMany_rename (fun x hx => h x (by
        simp only [termOperands, List.mem_cons, List.mem_append]
        split at hx <;> simp [hx]))]
    | _ => rfl
  | brTable x d tbl =>
    simp only [termEval, mapTerm, Res.norm_bind, Res.norm_pure]
    rw [hg x (by simp [termOperands])]
    cases (F.get x).norm with
    | ok xv =>
      simp only [Res.ok_bind]
      have hsel : (tbl.map (mapBlockCall σ))[xv.toNat]?.getD (mapBlockCall σ d) =
          mapBlockCall σ (tbl[xv.toNat]?.getD d) := by
        rw [List.getElem?_map]; cases tbl[xv.toNat]? <;> rfl
      rw [hsel]
      simp only [mapBlockCall]
      rw [getMany_rename (fun y hy => h y (by
        simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
        cases hq : tbl[xv.toNat]? with
        | none => rw [hq] at hy; exact .inl (.inr hy)
        | some q => rw [hq] at hy; exact .inr ⟨q, List.mem_of_getElem? hq, hy⟩))]
    | _ => rfl
  | ret xs => rfl
  | returnCall fn args => rfl
  | trap c => rfl

theorem termEval_brif_cond {F : Frame} {M : Mem} {c c' : ValueId} {th el : BlockCall}
    (h : F.regs c' = F.regs c) :
    (termEval F M (.brif c' th el)).norm = (termEval F M (.brif c th el)).norm := by
  simp only [termEval, Res.norm_bind, Frame.get, h, Res.norm_ofOption]

theorem effTerm_single (F : Frame) (M : Mem) (a : Inst) (t : Terminator) :
    effTerm F M [a] t = seqEval F M a t := by
  simp only [effTerm, seqEval]
  cases evalInst F M a with
  | ok p => obtain ⟨vs, m⟩ := p; cases vs <;> rfl
  | trap _ => rfl
  | stuck _ => rfl

/-- A conditional trap in front of both sides of a branch refinement. -/
theorem BrRefines.cons_trap {tb : BlockId → Option TrapCode} {F : Frame} {M : Mem} {a : Inst}
    {t1 t2 : Terminator} {E : List Inst} (ha : ∃ y code, a = .trapz y code ∨ a = .trapnz y code)
    (h : BrRefines tb (termEval F M t1) (effTerm F M E t2)) :
    BrRefines tb (effTerm F M [a] t1) (effTerm F M (a :: E) t2) := by
  obtain ⟨y, code, hi⟩ := ha
  have hTL := evalInst_trapLike (fr := F) (fr' := F) (M := M) (M' := M) hi rfl
  simp only [effTerm]
  cases he : evalInst F M a with
  | ok p =>
    obtain ⟨vs, M1⟩ := p
    obtain ⟨rfl, rfl, -⟩ := hTL.1 vs M1 he
    exact h
  | trap c => exact BrRefines.refl _ _
  | stuck msg => exact BrRefines.refl _ _

section Skel
variable {f : Function} {ρ : Valuation} {fr : Frame} {mem : Mem}
  {rules : SimplifyFn} {skel : SkeletonFn} {allowed skelOk : Inst → Bool} {cfg : Cfg} {bi : Nat}

theorem renamed_term {st1 st2 st3 : SState} {t t1 : Terminator} {M : Mem}
    (h1 : GInv f ρ fr mem st1) (h2 : GInv f ρ fr mem st2) (hm12 : Mono ρ fr mem st1 st2)
    (hm23 : Mono ρ fr mem st2 st3)
    (hr : (termEval (withRegs fr (gval ρ fr mem st2)) M t1).norm =
      (termEval (withRegs fr (gval ρ fr mem st2)) M t).norm)
    (hns : NotStuck (termEval (withRegs fr (gval ρ fr mem st1)) M t)) :
    (termEval (withRegs fr (gval ρ fr mem st3)) M t1).norm =
      (termEval (withRegs fr (gval ρ fr mem st1)) M t).norm := by
  have e12 := termEval_grow (gval_le h1 hm12) hns
  rw [e12] at hr
  have hns2 : NotStuck (termEval (withRegs fr (gval ρ fr mem st2)) M t1) := by
    intro msg hmsg
    rw [hmsg] at hr
    cases hc : termEval (withRegs fr (gval ρ fr mem st1)) M t with
    | stuck msg' => exact hns msg' hc
    | ok _ => rw [hc] at hr; cases hr
    | trap _ => rw [hc] at hr; cases hr
  rw [termEval_grow (gval_le h2 hm23) hns2, hr]

theorem skelTerm_spec (hS : SimplifySound rules) (hK : SkeletonSound skel) (hE : GoodEnv f fr mem) :
    ∀ fuel st t extra t'' st' ch, GInv f ρ fr mem st → (∀ y ∈ termOperands t, st.known y = true) →
      skelTerm skel rules allowed skelOk cfg bi fuel st t = (extra, t'', st', ch) →
      GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' ∧
        BrRefines (fun b => st.trapBlocks.get? b) (termEval (withRegs fr (gval ρ fr mem st')) mem t)
          (effTerm (withRegs fr (gval ρ fr mem st')) mem (effsOf extra) t'') := by
  intro fuel
  induction fuel with
  | zero =>
    intro st t extra t'' st' ch hI _ h
    simp only [skelTerm, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    exact ⟨hI, Mono.refl _, BrRefines.refl _ _⟩
  | succ fuel ih =>
    intro st t extra t'' st' ch hI hk h
    obtain ⟨hI1, hG1, hC1⟩ := runSkel_spec (allowed := allowed) hS hK hE hI (.term t)
    rw [skelTerm] at h
    generalize runSkel skel rules allowed st (.term t) = r at h hI1 hG1 hC1
    obtain ⟨c, st1⟩ := r
    simp only at h hI1 hG1 hC1
    have hM1 : Mono ρ fr mem st st1 := hG1.mono
    have hkeep : ((#[], t, st1, false) : Array Stmt × Terminator × SState × Bool) =
        (extra, t'', st', ch) → GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' ∧
          BrRefines (fun b => st.trapBlocks.get? b) (termEval (withRegs fr (gval ρ fr mem st')) mem t)
            (effTerm (withRegs fr (gval ρ fr mem st')) mem (effsOf extra) t'') := by
      intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      exact ⟨hI1, hM1, BrRefines.refl _ _⟩
    -- the source terminator, read later
    have hsrc : ∀ st3 : SState, Mono ρ fr mem st1 st3 →
        termEval (withRegs fr (gval ρ fr mem st3)) mem t =
          termEval (withRegs fr (gval ρ fr mem st1)) mem t := fun st3 hm =>
      termEval_congr (fun x hx => hm.fix x (hM1.known x (hk x hx)))
    split at h
    · -- replace
      rename_i t'
      have hR : BrRefines _ _ _ := hC1 _ rfl
      split at h
      · rename_i m st2 out2 hmat
        generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
          (mapTerm (rename m) t') = rr at h
        obtain ⟨more, t3, st3, ch3⟩ := rr
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, -⟩ := h
        obtain ⟨hI2, hG2, hmap, hps⟩ := materializeAll_spec hE hI1 hmat
        have hren := rename_spec hmap hps
        have hM2 : Mono ρ fr mem st1 st2 := hG2.mono
        obtain ⟨hI3, hM3, hB3⟩ := ih st2 _ more t3 st3 ch3 hI2 (by
          intro y hy
          rw [termOperands_mapTerm] at hy
          obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
          exact known_of_avail (hren y0 hy0).2) hrec
        refine ⟨hI3, hM1.trans (hM2.trans hM3), ?_⟩
        rw [effsOf_append, effsOf_pure (materializeAll_pure hmat), List.nil_append]
        rw [hM2.trap, hM1.trap] at hB3
        refine BrRefines.trans (BrRefines.grow hR (hsrc st3 (hM2.trans hM3)) (fun hns => ?_)) hB3
        exact renamed_term hI1 hI2 hM2 hM3
          (termEval_rename (fun y hy => (hren y hy).1)) hns
      · exact hkeep h
    · -- replaceBranchCond
      rename_i cv
      have hR := hC1 _ rfl
      cases hT : t
      case brif c0 th el =>
        rw [← hT]
        simp only [hT] at h hR
        split at h
        · rename_i m st2 out2 hmat
          generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
            (.brif (rename m cv) th el) = rr at h
          obtain ⟨more, t3, st3, ch3⟩ := rr
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, -⟩ := h
          obtain ⟨hI2, hG2, hmap, hps⟩ := materializeAll_spec hE hI1 hmat
          have hren := rename_spec hmap hps
          have hM2 : Mono ρ fr mem st1 st2 := hG2.mono
          obtain ⟨hI3, hM3, hB3⟩ := ih st2 _ more t3 st3 ch3 hI2 (by
            intro y hy
            simp only [termOperands, List.mem_append, List.mem_cons] at hy
            rcases hy with (rfl | hy) | hy
            · exact known_of_avail (hren cv (by simp)).2
            · exact hM2.known y (hM1.known y (hk y (by rw [hT]; simp [termOperands, hy])))
            · exact hM2.known y (hM1.known y (hk y (by rw [hT]; simp [termOperands, hy])))) hrec
          refine ⟨hI3, hM1.trans (hM2.trans hM3), ?_⟩
          rw [effsOf_append, effsOf_pure (materializeAll_pure hmat), List.nil_append]
          rw [hM2.trap, hM1.trap] at hB3
          refine BrRefines.trans (BrRefines.grow (by rw [hT]; exact hR) (hsrc st3 (hM2.trans hM3))
            (fun hns => ?_)) hB3
          exact renamed_term hI1 hI2 hM2 hM3 (termEval_brif_cond (hren cv (by simp)).1) hns
        · exact hkeep (by rw [hT]; exact h)
      all_goals (rw [← hT]; simp only [hT] at h; exact hkeep (by rw [hT]; exact h))
    · -- replaceWithTwo
      rename_i a t'
      have hR : BrRefines _ _ _ := hC1 _ rfl
      split at h
      · exact hkeep h
      · rename_i htl
        split at h
        · rename_i m st2 out2 hmat
          generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
            (mapTerm (rename m) t') = rr at h
          obtain ⟨more, t3, st3, ch3⟩ := rr
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, -⟩ := h
          obtain ⟨hI2, hG2, hmap, hps⟩ := materializeAll_spec hE hI1 hmat
          have hren := rename_spec hmap hps
          have hM2 : Mono ρ fr mem st1 st2 := hG2.mono
          obtain ⟨hI3, hM3, hB3⟩ := ih st2 _ more t3 st3 ch3 hI2 (by
            intro y hy
            rw [termOperands_mapTerm] at hy
            obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
            exact known_of_avail (hren y0 (List.mem_append_right _ hy0)).2) hrec
          refine ⟨hI3, hM1.trans (hM2.trans hM3), ?_⟩
          -- the trap prefix
          have hTLa : ∃ y code, a = .trapz y code ∨ a = .trapnz y code := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at htl
            have := htl.2
            cases a <;> simp [isTrapLike] at this
            · rename_i y code; exact ⟨y, code, .inl rfl⟩
            · rename_i y code; exact ⟨y, code, .inr rfl⟩
          obtain ⟨y, code, hay⟩ := hTLa
          have hTLa' : ∃ y code, mapOperands (rename m) a = .trapz y code ∨
              mapOperands (rename m) a = .trapnz y code := by
            rcases hay with rfl | rfl
            · exact ⟨_, code, .inl rfl⟩
            · exact ⟨_, code, .inr rfl⟩
          have hnp : isPure (mapOperands (rename m) a) = false := by
            rcases hay with rfl | rfl <;> rfl
          have heff : effsOf (out2 ++ #[{ inst := mapOperands (rename m) a }] ++ more) =
              mapOperands (rename m) a :: effsOf more := by
            rw [effsOf_append, effsOf_append, effsOf_pure (materializeAll_pure hmat)]
            simp [effsOf, hnp]
          rw [heff]
          rw [hM2.trap, hM1.trap] at hB3
          refine BrRefines.trans (BrRefines.grow hR (hsrc st3 (hM2.trans hM3)) (fun hns => ?_))
            (BrRefines.cons_trap hTLa' hB3)
          -- `seqEval a t'` read after the renaming
          rw [effTerm_single]
          have hna : NotStuck (evalInst (withRegs fr (gval ρ fr mem st1)) mem a) := by
            intro msg hmsg; simp only [seqEval, hmsg] at hns; exact hns msg rfl
          have hra := renamed_eval (st3 := st3) hI1 hI2 hM2 hM3
            (fun y hy => (hren y (List.mem_append_left _ hy)).1) hna
          simp only [seqEval]
          cases he : evalInst (withRegs fr (gval ρ fr mem st1)) mem a with
          | ok p =>
            obtain ⟨vs, M1⟩ := p
            rw [Res.norm_eq_ok hra he]
            obtain ⟨hvs, hM1, -⟩ := (evalInst_trapLike (fr := withRegs fr (gval ρ fr mem st1))
              (fr' := withRegs fr (gval ρ fr mem st1)) (M := mem) (M' := mem) hay rfl).1 vs M1 he
            subst hvs
            rw [hM1] at he ⊢
            have hnt : NotStuck (termEval (withRegs fr (gval ρ fr mem st1)) mem t') := by
              intro msg hmsg; simp only [seqEval, he, hmsg] at hns; exact hns msg rfl
            exact renamed_term hI1 hI2 hM2 hM3
              (termEval_rename (fun y hy => (hren y (List.mem_append_right _ hy)).1)) hnt
          | trap c => rw [Res.norm_eq_trap hra he]
          | stuck msg => exact absurd he (hna msg)
        · exact hkeep h
    · exact hkeep h

end Skel

/-! ## One statement -/

section Stmt
variable {f : Function} {ρ : Valuation} {fr : Frame} {mem : Mem}

/-- `stepStmt` enters the node of a new statement value `w` (below `next`, unknown) over available
operands. -/
theorem insertAt_spec {st st' : SState} (h : GInv f ρ fr mem st) (hE : GoodEnv f fr mem)
    {w : ValueId} {n : Inst} (hw : st.known w = false) (hwn : w < st.next)
    (hn : ∀ y ∈ operands n, st.avail.contains y = true) (hty : st.typedNode n = true)
    (htw : st.types.get? w = SState.nodeTy n)
    (hd : st'.defs = st.defs.insert w n) (ht : st'.types = st.types) (hnx : st'.next = st.next)
    (ha : st'.avail = st.avail) (hal : st'.alts = st.alts) (hm : st'.memo = st.memo)
    (hf : st'.fn = st.fn) (hc : st'.classes = {}) (hp : st'.partialVals = st.partialVals)
    (htr : st'.trapBlocks = st.trapBlocks) :
    GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' ∧ st'.solid w = true ∧
      gval ρ fr mem st' w = evalNode (withRegs fr (gval ρ fr mem st)) mem n ∧
      ∃ a, gval ρ fr mem st' w = some a := by
  have hnk : ∀ y ∈ operands n, st.known y = true := fun y hy => known_of_avail (hn y hy)
  obtain ⟨hfix, hnew⟩ := gval_insert h hw hnk hd
  obtain ⟨a, hev, hta⟩ := typed_total h hE hty (fun u hu => h.tot u (hn u hu) |>.imp fun _ h => h.1)
  have hwa : st.avail.contains w = false := (known_false hw).2
  have hdw : st'.defs.get? w = some n := by rw [hd, hm_get?_insert]; simp
  have hkw : st'.known w = true := known_of_defs hdw
  have hdx : ∀ x, x ≠ w → st'.defs.get? x = st.defs.get? x := by
    intro x hx; rw [hd, hm_get?_insert, if_neg (Ne.symm hx)]
  have hkm : ∀ x, st.known x = true → st'.known x = true := by
    intro x hx
    apply known_mono_defs _ _ hx
    · intro y hy
      by_cases hyw : y = w
      · rw [hyw, hdw]; rfl
      · rw [hdx y hyw]; exact hy
    · intro y hy; rw [ha]; exact hy
  have hkb : ∀ x, x ≠ w → st'.known x = true → st.known x = true := by
    intro x hxw hx
    cases hk : st.known x with
    | true => rfl
    | false =>
      obtain ⟨hd0, ha0⟩ := known_false hk
      simp only [SState.known, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · rw [Std.HashMap.contains_eq_isSome_getElem?] at hx
        have := hdx x hxw
        simp only [Std.HashMap.get?_eq_getElem?] at this hd0
        rw [this, hd0] at hx; cases hx
      · rw [ha] at hx; rw [hx] at ha0; cases ha0
  have hunk : ∀ x, x ≠ w → st.known x = false → gval ρ fr mem st' x = none := by
    intro x hx hk
    have hd' : st'.graph x = none := by
      simp only [SState.graph]; rw [hdx x hx]; exact (known_false hk).1
    rw [gval, den_leaf hd']
    cases hρ : ρ x with
    | none => rfl
    | some a => rw [known_of_avail (h.leaf x a hρ).1] at hk; cases hk
  have hpw : st.partialVals.contains w = false := by
    cases hc' : st.partialVals.contains w with
    | false => rfl
    | true => rw [h.partialKnown w hc'] at hw; cases hw
  have hsw : st'.solid w = true := by
    simp only [SState.solid, hkw, hp, hpw, Bool.not_false, Bool.and_self]
  have hsm : ∀ x, st.solid x = true → st'.solid x = true := by
    intro x hx
    simp only [SState.solid, Bool.and_eq_true, Bool.not_eq_true'] at hx ⊢
    exact ⟨hkm x hx.1, by rw [hp]; exact hx.2⟩
  have hgw : gval ρ fr mem st' w = some a := by rw [hnew, hev]
  refine ⟨⟨hf.trans h.fn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hkm, hfix, htr, hf⟩, hsw,
    hnew, a, hgw⟩
  · intro x m hx y hy
    by_cases hxw : x = w
    · rw [hxw, hdw] at hx; cases hx; exact hkm y (hnk y hy)
    · rw [hdx x hxw] at hx; exact hkm y (h.closed x m hx y hy)
  · intro x hx
    rw [hnx]
    by_cases hxw : x = w
    · rw [hxw]; exact hwn
    · exact h.fresh x (hkb x hxw hx)
  · intro x hx; rw [hnx] at hx; exact h.freshρ x hx
  · intro x a' hx
    obtain ⟨h1', h2'⟩ := h.leaf x a' hx
    have hxw : x ≠ w := by intro he; rw [he] at h1'; rw [h1'] at hwa; cases hwa
    exact ⟨by rw [ha]; exact h1', by rw [hdx x hxw]; exact h2'⟩
  · intro x hx
    rw [ha] at hx
    obtain ⟨a', h1', h2'⟩ := h.tot x hx
    exact ⟨a', by rw [hfix x (known_of_avail hx)]; exact h1', by rw [ht]; exact h2'⟩
  · intro x t a' hx hv
    rw [ht] at hx
    by_cases hxw : x = w
    · subst hxw
      rw [hgw] at hv; cases hv
      rw [htw, hta] at hx; exact (Option.some.inj hx)
    · cases hk : st.known x with
      | true => rw [hfix x hk] at hv; exact h.types x t a' hx hv
      | false => rw [hunk x hxw hk] at hv; cases hv
  · intro x ms hx
    rw [hal] at hx
    obtain ⟨hk, hms⟩ := h.alts x ms hx
    refine ⟨hkm x hk, fun m hm a' hv => ?_⟩
    rw [hfix x hk] at hv
    have := hms m hm a' hv
    rw [hfix m (known_of_gval h this)]; exact this
  · intro n' w' hx
    rw [hm] at hx
    obtain ⟨hk, hw'⟩ := h.memo n' w' hx
    refine ⟨fun y hy => hkm y (hk y hy), fun a' hv => ?_⟩
    rw [evalNode_congr (fr := withRegs fr (gval ρ fr mem st)) (fr' := withRegs fr (gval ρ fr mem st'))
      rfl rfl (fun y hy => hfix y (hk y hy))] at hv
    have := hw' a' hv
    rw [hfix w' (known_of_gval h this)]; exact this
  · intro x hx
    rw [hp] at hx; exact hkm x (h.partialKnown x hx)
  · intro x hx
    by_cases hxw : x = w
    · subst hxw; exact ⟨a, hgw, by rw [ht, htw, hta]⟩
    · have hxs : st.solid x = true := by
        simp only [SState.solid, Bool.and_eq_true, Bool.not_eq_true'] at hx ⊢
        exact ⟨hkb x hxw hx.1, by rw [← hp]; exact hx.2⟩
      obtain ⟨a', h1', h2'⟩ := h.solid x hxs
      have hk : st.known x = true := by
        simp only [SState.solid, Bool.and_eq_true] at hxs; exact hxs.1
      exact ⟨a', by rw [hfix x hk]; exact h1', by rw [ht]; exact h2'⟩
  · intro k ms hx
    rw [hc] at hx; simp at hx

/-- A defined, typed graph value becomes available. -/
theorem availInsert_spec {st st' : SState} (h : GInv f ρ fr mem st) {x : ValueId} {bi : Nat}
    (hx : st.known x = true) (hxv : ∃ a, gval ρ fr mem st x = some a ∧ st.types.get? x = some a.ty)
    (ha : st'.avail = st.avail.insert x bi) (hd : st'.defs = st.defs) (ht : st'.types = st.types)
    (hf : st'.fn = st.fn) (hn : st'.next = st.next) (hp : st'.partialVals = st.partialVals)
    (hal : st'.alts = st.alts) (hm : st'.memo = st.memo) (hc : st'.classes = st.classes)
    (htr : st'.trapBlocks = st.trapBlocks) :
    GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' := by
  have hgr : st'.graph = st.graph := by funext y; simp [SState.graph, hd]
  have hg : gval ρ fr mem st' = gval ρ fr mem st := by simp only [gval, hgr]
  have hk : ∀ y, st'.known y = (st.known y || x == y) := by
    intro y
    simp only [SState.known, hd, ha, hm_contains_insert]
    cases st.defs.contains y <;> cases st.avail.contains y <;> cases x == y <;> rfl
  have hkm : ∀ y, st.known y = true → st'.known y = true := by
    intro y hy; rw [hk, hy]; rfl
  have hkb : ∀ y, st'.known y = true → st.known y = true := by
    intro y hy; rw [hk] at hy
    simp only [Bool.or_eq_true, beq_iff_eq] at hy
    rcases hy with hy | rfl
    · exact hy
    · exact hx
  have hs : ∀ y, st'.solid y = st.solid y := by
    intro y
    simp only [SState.solid, hp]
    cases hky : st.known y
    · have : st'.known y = false := by
        cases h' : st'.known y
        · rfl
        · rw [hkb y h'] at hky; cases hky
      rw [this]
    · rw [hkm y hky]
  refine ⟨⟨hf.trans h.fn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Mono.of_graph hd (fun y hy => by rw [ha, hm_contains_insert]; simp [hy]) htr hf⟩
  · intro y m hy z hz; rw [hd] at hy; exact hkm z (h.closed y m hy z hz)
  · intro y hy; rw [hn]; exact h.fresh y (hkb y hy)
  · intro y hy; rw [hn] at hy; exact h.freshρ y hy
  · intro y a hy
    obtain ⟨h1, h2⟩ := h.leaf y a hy
    exact ⟨by rw [ha, hm_contains_insert]; simp [h1], by rw [hd]; exact h2⟩
  · intro y hy
    rw [ha, hm_contains_insert] at hy
    simp only [Bool.or_eq_true, beq_iff_eq] at hy
    rw [hg, ht]
    rcases hy with rfl | hy
    · exact hxv
    · exact h.tot y hy
  · intro y t a hy hv; rw [hg] at hv; rw [ht] at hy; exact h.types y t a hy hv
  · intro y ms hy; rw [hal] at hy; rw [hg]
    obtain ⟨h1, h2⟩ := h.alts y ms hy
    exact ⟨hkm y h1, h2⟩
  · intro n w hy; rw [hm] at hy; rw [hg]
    obtain ⟨h1, h2⟩ := h.memo n w hy
    exact ⟨fun z hz => hkm z (h1 z hz), h2⟩
  · intro y hy; rw [hp] at hy; exact hkm y (h.partialKnown y hy)
  · intro y hy; rw [hs] at hy; rw [hg, ht]; exact h.solid y hy
  · intro k ms hy; rw [hc] at hy
    obtain ⟨o, ho, h2⟩ := h.classes k ms hy
    exact ⟨o, by rw [hs]; exact ho, by rw [hg]; exact h2⟩

/-- Recording the alternatives of a value. -/
theorem altsInsert_spec {st st' : SState} (h : GInv f ρ fr mem st) {x : ValueId}
    {ms : List ValueId} (hx : st.known x = true)
    (hms : ∀ m ∈ ms, ∀ a, gval ρ fr mem st x = some a → gval ρ fr mem st m = some a)
    (hal : st'.alts = st.alts.insert x ms) (hd : st'.defs = st.defs) (ha : st'.avail = st.avail)
    (ht : st'.types = st.types) (hf : st'.fn = st.fn) (hn : st'.next = st.next)
    (hp : st'.partialVals = st.partialVals) (hm : st'.memo = st.memo)
    (hc : st'.classes = st.classes) (htr : st'.trapBlocks = st.trapBlocks) :
    GInv f ρ fr mem st' ∧ Mono ρ fr mem st st' := by
  refine ⟨h.of_graph hd ha ht hf (by rw [hn]; exact Nat.le_refl _) hp ?_ (by rw [hm]; exact h.memo)
    (by rw [hc]; exact h.classes), Mono.of_graph hd (fun y hy => by rw [ha]; exact hy) htr hf⟩
  intro y ms' hy
  rw [hal, hm_get?_insert] at hy
  split at hy
  · rename_i he; subst he; cases hy; exact ⟨hx, hms⟩
  · exact h.alts y ms' hy

end Stmt

end Opt
