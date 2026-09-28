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

end Opt
