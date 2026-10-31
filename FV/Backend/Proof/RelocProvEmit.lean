import FV.Backend.Proof.FrameLines
import FV.Backend.Proof.RelocProvDefs
import FV.E2E.EmitPreOk
import FV.E2E.PairLines
import FV.Backend.Proof.EncodeLayout
import FV.Backend.Proof.DeadCleanupPrepare

/-!
# Name provenance of the compiled relocations: the backend tail (L1e, #216)

`relocs_of_alloc`: if every instruction of the prepared VCode has its references in `f`
(`AllInsts (RefsOk f)`), every relocation of the laid-out function relocates against a name
(and addend) of `f` (`RelocOk f`). The steps after the ISLE lowering:

* **`prune`, `prepare`** (`prune_allInsts`, `prepare_allInsts`): `prune` only deletes
  instructions; `prepare` keeps the input's instructions, retargets terminators (`setTargets`
  keeps a call's symbol, `refsOk_setTargets`) and adds edge blocks of a single `jump`.
* **Allocation** (`lowerRFunc_refsOk`): the instructions of the allocated function are the
  prepared ones with their registers substituted (`MInst.assign` only rewrites registers:
  `refsOk_assign`), and the moves' `mov`/`ldr`/`str`/`movz`/`movk`/`add`, which reference
  nothing.
* **Emission** (`emitFunc_lnOk`): `LnOk f` of a line: a `bl`'s symbol is an external
  function's name, an `adrp …, :got:`'s symbol is a declared name, an `adrp`'s symbol and addend
  are a declared name and offset. `MInst.lines` of a call gives `bl n`, of `loadExtNameGot rd n`
  `adrp :got:`/`ldr :got_lo12:`, of `loadExtNameNear rd n off` `adrp`/`add :lo12:` with addend
  `off`; every other expansion (prologue, epilogue, moves, traps, TLS, atomics) has no such
  line. `fallthrough` and branch relaxation only drop branches or rewrite conditional branches.
* **Layout**: the relocations are those of the code lines (`mem_codeRelocs`).
-/

namespace Backend.Proof.RelocProv

open Backend Backend.Proof E2E

/-! ## Retargeting, renaming, register substitution -/

/-- **Retargeting keeps the references.** -/
theorem refsOk_setTargets {f : Clif.Function} {t t' : MInst} {ls : List Label}
    (h : t.setTargets ls = some t') (ht : RefsOk f t) : RefsOk f t' := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals first | cases h | (simp only [Option.some.injEq] at h; subst h)
  all_goals first | exact trivial | exact ht

/-- **Renaming registers keeps the references.** -/
theorem refsOk_mapRegs {f : Clif.Function} (R : Reg → Reg) (m : MInst) :
    RefsOk f (m.mapRegs R) ↔ RefsOk f m := by
  cases m
  case call info =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp [MInst.mapRegs, RefsOk]
  case tryCall info ti =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp [MInst.mapRegs, RefsOk]
  all_goals exact Iff.rfl

/-- The substitution step keeps the references. -/
theorem refsOk_visit {f : Clif.Function} (regs : Array Reg) (i : MInst) :
    PutPost (MInst.visitOperands (putOp regs) i) (fun m => RefsOk f i → RefsOk f m) := by
  cases i
  case call info =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.visitOperands, pure_bind] <;>
      repeat' first | (with_reducible apply putPost_bind); intro _ | (with_reducible apply putPost_pure)
    all_goals first | exact fun h => h | (intro _ n hn; simp at hn)
  case tryCall info ti =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.visitOperands, pure_bind] <;>
      repeat' first | (with_reducible apply putPost_bind); intro _ | (with_reducible apply putPost_pure)
    all_goals first | exact fun h => h | (intro _ n hn; simp at hn)
  all_goals
    simp only [MInst.visitOperands]
    repeat' first | (with_reducible apply putPost_bind); intro _ | (with_reducible apply putPost_pure)
  all_goals first | exact fun _ => trivial | exact fun h => h

/-- **Substituting an allocation keeps the references.** -/
theorem refsOk_assign {f : Clif.Function} {i m : MInst} {regs : Array Reg}
    (h : i.assign regs = .ok m) (hi : RefsOk f i) : RefsOk f m :=
  assign_post h (refsOk_visit regs i) hi

/-! ## `prune` and `prepare` -/

/-- **`prepare` keeps an instruction property** that holds of `jump`s and survives
retargeting. -/
theorem prepare_allInsts {P : MInst → Prop} (hj : ∀ l, P (.jump l))
    (hset : ∀ t ls t', t.setTargets ls = some t' → P t → P t') {vc vcp : VCode}
    (hp : prepare vc = .ok vcp) (h : AllInsts P vc) : AllInsts P vcp := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, -, -, hS, -, rfl⟩ := Prep.prepare_facts hp
  intro vb hvb m hm
  simp only [Array.toList_map, List.mem_map] at hvb
  obtain ⟨i, -, rfl⟩ := hvb
  by_cases hi2 : i < (B ++ E).size
  · rw [getElem!_pos (B ++ E) i hi2] at hm
    by_cases hiB : i < B.size
    · rw [Array.getElem_append_left hiB] at hm
      have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← hS.size]; exact hiB
      obtain ⟨b, hb, e, -⟩ := Prep.keep_src hi1
      have hmem : (Prep.keep vc.blocks (reachable ss0))[i] ∈ vc.blocks.toList := by rw [e]; simp
      rcases hS.rw i hi1 hiB with h' | ⟨t, t', ls, h1, -, h3, h4, -⟩
      · rw [h'] at hm; exact h _ hmem m hm
      · rw [h4] at hm
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact h _ hmem m (Prep.pop_mem hm)
        · exact hset t ls _ h3 (h _ hmem t (Array.mem_toList_iff.mpr (Array.mem_of_back? h1)))
    · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)] at hm
      have he : i - B.size < E.size := by simp at hi2; omega
      obtain ⟨l, hl⟩ := hS.edges _ he
      rw [hl] at hm
      simp at hm
      subst hm
      exact hj l
  · rw [getElem!_neg (B ++ E) i hi2] at hm
    cases hm

/-- **`prune` keeps every instruction property** (it only deletes instructions). -/
theorem prune_allInsts {P : MInst → Prop} {vc : VCode} (h : AllInsts P vc) :
    AllInsts P (DeadCleanup.prune vc) :=
  DeadCleanup.prune_insts h

/-! ## Allocation -/

theorem slotStoreAt_refsOk {f : Clif.Function} (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotStoreAt cls r off, RefsOk f m := by
  intro m hm
  unfold slotStoreAt spAddrX16 at hm
  split at hm
  · simp only [List.mem_singleton] at hm; subst hm; cases cls <;> exact trivial
  · simp only [List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, List.nil_append, or_false] at hm
    rcases hm with rfl | ⟨_, -, rfl⟩ | rfl | rfl
    all_goals first | exact trivial | (cases cls <;> exact trivial)

theorem slotLoadAt_refsOk {f : Clif.Function} (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotLoadAt cls r off, RefsOk f m := by
  intro m hm
  unfold slotLoadAt spAddrX16 at hm
  split at hm
  · simp only [List.mem_singleton] at hm; subst hm; cases cls <;> exact trivial
  · simp only [List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, List.nil_append, or_false] at hm
    rcases hm with rfl | ⟨_, -, rfl⟩ | rfl | rfl
    all_goals first | exact trivial | (cases cls <;> exact trivial)

/-- The instructions of a move reference nothing. -/
theorem moveInsts_refsOk {f : Clif.Function} {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : ∀ m, AInst.inst m ∈ l → RefsOk f m := by
  intro m hm
  unfold RAFrame.moveInsts at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; cases hm
  · cases h; cases hm
  · split at h
    · cases h
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm
      exact trivial
    · cases h
      rcases List.mem_append.mp (mem_map_inst hm) with h | h
      · exact slotStoreAt_refsOk _ _ _ m h
      · exact slotLoadAt_refsOk _ _ _ m h
  · split at h
    · cases h
    · cases h
      exact slotStoreAt_refsOk _ _ _ m (mem_map_inst hm)
  · split at h
    · cases h
    · cases h
      exact slotLoadAt_refsOk _ _ _ m (mem_map_inst hm)
  · cases h

/-- **The allocated function's instructions have their references in `f`** if the prepared
VCode's do. -/
theorem lowerRFunc_refsOk {f : Clif.Function} {vcp : VCode} {rf : RFunc} {af : AFunc}
    (hv : AllInsts (RefsOk f) vcp) (hal : lowerRFunc vcp rf = .ok af) :
    ∀ x ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ x.2.toList → RefsOk f m := by
  intro x hx m hm
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hx
  rw [Array.getElem?_toList] at hb
  obtain ⟨l, code⟩ := x
  obtain ⟨⟨-, -, hsz, hbl⟩, -, -⟩ := lowerRFunc_ok hal
  have hlt : b < (vcp.blocks.zip rf.blocks).size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hb).1
  rw [Array.size_zip] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, vcp.blocks[b]? = some vb :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, rf.blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cd, hcd, hb'⟩ := hbl b vb items hvb hit
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  have hm' : AInst.inst m ∈ cd := by simpa using hm
  obtain ⟨it, -, c1, hc1, hmc⟩ := mem_itemsCode hcd hm'
  cases it with
  | move src dst => exact moveInsts_refsOk (itemCode_move_ok hc1) m hmc
  | op kk allocs =>
    obtain ⟨regs, i, i', -, hi, hasg, hcase⟩ := itemCode_op hc1
    have hvbm : vb ∈ vcp.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb)
    have hio : RefsOk f i := hv vb hvbm i (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    rcases hcase with ⟨rfl, -, -⟩ | ⟨ds, -, rfl⟩ | ⟨us, -, rfl⟩
    · simp only [List.mem_singleton, AInst.inst.injEq] at hmc
      subst hmc
      exact refsOk_assign hasg hio
    · cases hmc
    · simp at hmc

/-! ## Lines -/

/-- An instruction without a reference to check (not `bl`, `adrp …, :got:`, `adrp`). -/
def refFreeI : Insn → Bool
  | .bl _ | .adrpGot .. | .adrp .. => false
  | _ => true

/-- A line without a reference to check. -/
def refFreeL : Line → Bool
  | .ins i _ => refFreeI i
  | _ => true

/-- **The references of an instruction are `f`'s**, by the relocation it gets. -/
def InsnOk (f : Clif.Function) : Insn → Prop
  | .bl s => s ∈ externNames f
  | .adrpGot _ s => s ∈ refNames f
  | .adrp _ s a => s ∈ refNames f ∧ a ∈ refOffs f
  | _ => True

/-- The references of a line are `f`'s. -/
def LnOk (f : Clif.Function) : Line → Prop
  | .ins i _ => InsnOk f i
  | _ => True

theorem lnOk_of_free {f : Clif.Function} {ln : Line} (h : refFreeL ln = true) : LnOk f ln := by
  cases ln with
  | ins i t => cases i <;> first | exact trivial | cases h
  | _ => exact trivial

theorem lnOk_of_all_free {f : Clif.Function} {L : List Line} (h : ∀ ln ∈ L, refFreeL ln = true) :
    ∀ ln ∈ L, LnOk f ln :=
  fun ln hln => lnOk_of_free (h ln hln)

/-- A relocation of an instruction with `InsnOk f` is `f`'s. -/
theorem insnOk_reloc {f : Clif.Function} {i : Insn} (h : InsnOk f i) {ty : RelocType} {s : String}
    {a : Int} (hr : i.reloc? = some (ty, s, a)) (o : Nat) : RelocOk f ⟨o, ty, s, a⟩ := by
  cases i <;> simp only [Insn.reloc?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, rfl⟩ := hr
  all_goals first | exact trivial | exact h | exact ⟨h, List.mem_cons_self ..⟩

theorem insnOk_invertTo {f : Clif.Function} {c : Insn} (e : Lbl) (h : InsnOk f c) :
    InsnOk f (c.invertTo e) := by
  cases c <;> first | exact h | exact trivial

theorem loadConst64_free (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, refFreeL ln = true := by
  intro ln h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · simp only [Option.some.injEq] at hj; subst hj; rfl
    · cases hj

theorem memFinalize_free {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (hm : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, refFreeL ln = true := by
  obtain ⟨pre, am⟩ := v
  intro ln hln
  unfold memFinalize at hm
  have hfin : ∀ (base : Reg) (off : Int) pre am,
      (match simm9? off with
        | some s => (([] : List Line), AMode.unscaled base s)
        | none => match uimm12Scaled? off b with
          | some o => ([], .unsignedOffset base o)
          | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (pre, am) →
      ln ∈ pre → refFreeL ln = true := by
    intro base off pre am e hin
    split at e
    · cases e; simp at hin
    · split at e
      · cases e; simp at hin
      · cases e
        exact loadConst64_free _ _ _ hin
  split at hm <;> simp only [pure, Except.pure, Except.ok.injEq] at hm <;>
    first | exact hfin _ _ _ _ hm hln | (cases hm; simp at hln) | cases hm

@[simp] theorem CondBrKind.insn_free (k : CondBrKind) (l : Lbl) : refFreeI (k.insn l) = true := by
  cases k <;> rfl

@[simp] theorem casLoopCmp_free (bits : Nat) : refFreeI (casLoopCmp bits) = true := by
  unfold casLoopCmp; split <;> rfl

@[simp] theorem rmwLoopCmp_free (op : AtomicRmwLoopOp) (bits : Nat) :
    refFreeI (rmwLoopCmp op bits) = true := by
  unfold rmwLoopCmp; split <;> rfl

@[simp] theorem rmwLoopSext_free (bits : Nat) : ∀ i ∈ rmwLoopSext bits, refFreeI i = true := by
  unfold rmwLoopSext; split <;> simp <;> rfl

@[simp] theorem rmwLoopMid_free (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, refFreeI i = true := by
  cases op <;> simp [rmwLoopMid, or_imp, forall_and] <;> (repeat' constructor) <;>
    exact rmwLoopSext_free bits

/-- **The lines of an instruction without references** reference nothing. -/
theorem lines_free {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (hc : ∀ info, m ≠ .call info) (ht : ∀ info ti, m ≠ .tryCall info ti)
    (hg : ∀ rd n, m ≠ .loadExtNameGot rd n) (hn : ∀ rd n o, m ≠ .loadExtNameNear rd n o)
    (h : m.lines c ps = .ok (ls, ps')) : ∀ ln ∈ ls, refFreeL ln = true := by
  cases m
  case call info => exact absurd rfl (hc info)
  case tryCall info ti => exact absurd rfl (ht info ti)
  case loadExtNameGot rd n => exact absurd rfl (hg rd n)
  case loadExtNameNear rd n o => exact absurd rfl (hn rd n o)
  all_goals unfold MInst.lines at h
  all_goals simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals simp [refFreeL, refFreeI, MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines,
    casLoopHead, or_imp, forall_and]
  all_goals (repeat' constructor)
  all_goals first
    | exact memFinalize_free ‹_›
    | exact rmwLoopMid_free _ _
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | ((repeat' split) <;> first
        | (simp <;> rfl)
        | (rename_i heq; have h' := congrArg refFreeI heq
           simp only [CondBrKind.insn_free, casLoopCmp_free] at h'; simp [refFreeI] at h'))

/-- **The lines of an instruction with its references in `f`** are `LnOk f`. -/
theorem lines_ok {f : Clif.Function} {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (hm : RefsOk f m) (h : m.lines c ps = .ok (ls, ps')) : ∀ ln ∈ ls, LnOk f ln := by
  cases m
  case call info =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> intro ln hln <;> simp only [List.mem_singleton] at hln <;> subst hln
    all_goals first | exact trivial | exact hm _ rfl
  case tryCall info ti =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> intro ln hln <;> simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hln <;> rcases hln with rfl | rfl
    all_goals first | exact trivial | exact hm _ rfl
  case loadExtNameGot rd n =>
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro ln hln
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
    rcases hln with rfl | rfl
    · exact hm
    · exact trivial
  case loadExtNameNear rd n o =>
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro ln hln
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
    rcases hln with rfl | rfl
    · exact hm
    · exact trivial
  all_goals exact lnOk_of_all_free (lines_free (fun _ e => by cases e) (fun _ _ e => by cases e)
    (fun _ _ e => by cases e) (fun _ _ _ e => by cases e) h)

/-! ## Emission -/

theorem prologueLines_free {calls : Bool} (saves : List Reg) (size : Nat) :
    ∀ ln ∈ prologueLines saves size calls, refFreeL ln = true := by
  intro ln hl
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((((rfl | rfl) | hl) | hl) | hl) | hl
  · exact rfl
  · exact rfl
  · rcases probeLines_mem hl with rfl | rfl | ⟨_, rfl⟩ | hl | hl | rfl | rfl | rfl | rfl <;>
      (try obtain ⟨_, rfl | rfl⟩ := loadConst64_mem hl) <;> exact rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> exact rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> exact rfl
  · rcases mem_spAdjLines hl with ⟨i, -, rfl⟩ | hl | rfl
    · exact rfl
    · exact loadConst64_free _ _ _ hl
    · exact rfl

theorem epilogueLines_free (saves : List Reg) (size : Nat) :
    ∀ ln ∈ epilogueLines saves size, refFreeL ln = true := by
  intro ln hl
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((hl | hl) | hl) | rfl | rfl
  · rcases mem_spAdjLines hl with ⟨i, -, rfl⟩ | hl | rfl
    · exact rfl
    · exact loadConst64_free _ _ _ hl
    · exact rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_popLines hl <;> exact rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_popLines hl <;> exact rfl
  · exact rfl
  · exact rfl

/-- `f`'s allocated code: every instruction has its references in `f`. -/
def CodeOk (f : Clif.Function) (code : List AInst) : Prop := ∀ m, AInst.inst m ∈ code → RefsOk f m

theorem ainstLines_ok {f : Clif.Function} {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState}
    {ls : List Line} (ha : ∀ m, a = .inst m → RefsOk f m)
    (h : ainstLines c af a ps = .ok (ls, ps')) : ∀ ln ∈ ls, LnOk f ln := by
  cases a with
  | inst m => exact lines_ok (ha m rfl) h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact lnOk_of_all_free (prologueLines_free _ _)
    · simp
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact lnOk_of_all_free (epilogueLines_free _ _)
    · intro ln hln; simp only [List.mem_singleton] at hln; subst hln; exact trivial

theorem codeLinesE_ok {f : Clif.Function} {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line), CodeOk f code →
      codeLinesE c af code ps = .ok (ls, ps') → ∀ ln ∈ ls, LnOk f ln
  | [], ps, ps', ls, _, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | a :: as, ps, ps', ls, hc, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro ln hln
        rcases List.mem_append.1 hln with h1 | h1
        · exact ainstLines_ok (fun m e => hc m (by rw [← e]; exact List.mem_cons_self ..)) hr ln h1
        · exact codeLinesE_ok as _ _ _ (fun m hm => hc m (List.mem_cons_of_mem _ hm)) hr2 ln h1

theorem blocksLinesE_ok {f : Clif.Function} {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (ls : List Line),
      (∀ x ∈ bs, CodeOk f x.2.toList) →
      blocksLinesE c af bs ps = .ok (ls, ps') → ∀ ln ∈ ls, LnOk f ln
  | [], ps, ps', ls, _, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | (l, code) :: bs, ps, ps', ls, hc, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro ln hln
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hln
        rcases hln with rfl | h1 | h1
        · exact trivial
        · exact codeLinesE_ok _ _ _ _ (hc _ (List.mem_cons_self ..)) hr ln h1
        · exact blocksLinesE_ok bs _ _ _ (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hr2 ln h1

theorem trapLines_ok {f : Clif.Function} (ts : List (Lbl × Clif.TrapCode)) :
    ∀ ln ∈ trapLines ts, LnOk f ln := by
  intro ln hln
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hln
  obtain ⟨p, -, rfl | rfl⟩ := hln <;> exact trivial

theorem ftList_ok {f : Clif.Function} : ∀ (n : Nat) (L : List Line), L.length ≤ n →
    (∀ ln ∈ L, LnOk f ln) → ∀ ln ∈ ftList L, LnOk f ln
  | _, [], _, _ => by simp [ftList]
  | n + 1, ln :: rest, hn, h => by
    rw [ftList_cons]
    have hrest : ∀ k, ∀ x ∈ (ln :: rest).drop k, LnOk f x :=
      fun k x hx => h x (List.mem_of_mem_drop hx)
    rcases ftStep_cases ln rest[0]? rest[1]? with he | ⟨x, l, rfl, h1, he⟩ | ⟨c, e, l, rfl, hc, h1, h2, he⟩
    · rw [he]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · simp only [List.mem_singleton] at hy; subst hy; exact h _ (List.mem_cons_self ..)
      · exact ftList_ok n _ (by simp at hn ⊢; omega) (hrest 1) y hy
    · rw [he]
      intro y hy
      simp only [List.nil_append] at hy
      exact ftList_ok n _ (by simp at hn ⊢; omega) (hrest 1) y hy
    · rw [he]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · simp only [List.mem_singleton] at hy; subst hy
        exact insnOk_invertTo e (h _ (List.mem_cons_self ..))
      · cases rest with
        | nil => simp at h1
        | cons _ _ => exact ftList_ok n _ (by simp at hn ⊢; omega) (hrest 2) y hy

theorem relaxLines_ok {f : Clif.Function} (F : Lbl → Bool) : ∀ (L : List Line),
    (∀ ln ∈ L, LnOk f ln) → ∀ ln ∈ relaxLines F L, LnOk f ln
  | [], _ => by simp [relaxLines]
  | ln :: L, h => by
    rw [relaxLines_cons]
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · have h0 := h ln (List.mem_cons_self ..)
      match ln, h0, hy with
      | .ins c (some tc), h0, hy => simp only [relaxLine, Line.relaxable?, List.mem_singleton] at hy; subst hy; exact h0
      | .label l, _, hy => simp only [relaxLine, Line.relaxable?, List.mem_singleton] at hy; subst hy; exact trivial
      | .word x z, _, hy => simp only [relaxLine, Line.relaxable?, List.mem_singleton] at hy; subst hy; exact trivial
      | .ins c none, h0, hy =>
        rcases relaxLine_cases F c with hr | ⟨t, -, hr⟩
        · rw [hr] at hy; simp only [List.mem_singleton] at hy; subst hy; exact h0
        · rw [hr] at hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact insnOk_invertTo _ h0
          · exact trivial
    · exact relaxLines_ok F L (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- **`emitFunc`'s lines are `LnOk f`** when the allocated code's instructions have their
references in `f`. -/
theorem emitFunc_lnOk {f : Clif.Function} {k : Nat} {af : AFunc} {fa : FnAsm}
    (hc : ∀ x ∈ af.blocks.toList, CodeOk f x.2.toList) (h : emitFunc k af = .ok fa) :
    ∀ ln ∈ fa.lines.toList, LnOk f ln := by
  obtain ⟨body, ps, hb, hl, -⟩ := emitFunc_ok h
  rw [hl]
  refine relaxLines_ok _ _ ?_
  intro ln hln
  rcases List.mem_append.1 hln with h1 | h1
  · exact ftList_ok _ _ (Nat.le_refl _) (blocksLinesE_ok _ _ _ _ hc hb) ln h1
  · exact trapLines_ok _ ln h1

/-! ## Layout -/

/-- **Name provenance of the backend tail**: if every instruction of the prepared VCode has its
references in `f`, every relocation of the compiled function is `f`'s. -/
theorem relocs_of_alloc {f : Clif.Function} {vcp : VCode} {rf : RFunc} {af : AFunc} {k : Nat}
    {fa : FnAsm} {fb : FnBin} (hv : AllInsts (RefsOk f) vcp) (hal : lowerRFunc vcp rf = .ok af)
    (hem : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) : ∀ r ∈ fb.relocs, RelocOk f r := by
  intro r hr
  obtain ⟨-, -, -, -, -, hrel, -⟩ := FnAsm.layout_unfold hla
  rw [hrel, mem_codeRelocs] at hr
  obtain ⟨j, i, t, hj, hi, -⟩ := hr
  have hmem : Line.ins i t ∈ fa.lines.toList :=
    (List.mem_filter.1 (List.mem_of_getElem? hj)).1
  have hok := emitFunc_lnOk (lowerRFunc_refsOk hv hal) hem _ hmem
  obtain ⟨o, ty, s, a⟩ := r
  exact insnOk_reloc hok hi o

end Backend.Proof.RelocProv
