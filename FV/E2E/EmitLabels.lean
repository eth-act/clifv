import FV.Backend.Proof.RelaxLayout
import FV.E2E.EmitCondsDefs
import FV.E2E.RegLevelEmit
import FV.Backend.Proof.AssignOk
import FV.E2E.AllocTotal
import FV.E2E.RegLevelOp
import FV.E2E.RegLevelSim

/-!
# The labels of the spill allocation's code (V6b)

`E2E.emitFunc_spill_labels`: the code `emitFunc` produces from the spill allocation of an in-scope
function defines every label once (`labelOffsets` succeeds) and every label operand names a
defined label — the first two premises of `emitFunc_layout_total`.

The emitted lines are tracked as `Chunk`s: the labels a piece of code defines (block labels, the
jump-table and atomic-loop labels of the counters' new range) are distinct, and every label it
uses is defined in it, a deferred trap's (`.trap n`, pushed with its use) or a block label among
the branch targets. `fallthrough` (`ftList`) and relaxation (`relaxLines`) keep the defined labels
and use no new one (`ftList_spec`, `relaxLines_spec`). The block labels are distinct
(`prepare_labels_nodup`); the allocated instructions keep the VCode's branch targets
(`assign_targets`, `itemsCode_targets`). That every branch target of the prepared VCode is a block
label is the decidable premise `branchTargetsOkB` (`VCode.cfg` checks it for the last instruction
of each block only; a branch in the middle of a block is not excluded by a lemma about the
lowering).
-/

namespace E2E.EmitLabels

open Backend

/-- The label a line defines. -/
def lineDef : Line → Option Lbl
  | .label l => some l
  | _ => none

/-- The labels a line list defines, in order. -/
def defs (L : List Line) : List Lbl := L.filterMap lineDef

/-- The labels a line list's label operands name. -/
def uses (L : List Line) : List Lbl := L.flatMap Line.labelsUsed

@[simp] theorem defs_nil : defs [] = [] := rfl

@[simp] theorem defs_cons (ln : Line) (L : List Line) :
    defs (ln :: L) = (lineDef ln).toList ++ defs L := by
  cases h : lineDef ln <;> simp [defs, h]

@[simp] theorem defs_append (A B : List Line) : defs (A ++ B) = defs A ++ defs B := by
  simp [defs, List.filterMap_append]

@[simp] theorem uses_nil : uses [] = [] := rfl

@[simp] theorem uses_cons (ln : Line) (L : List Line) : uses (ln :: L) = ln.labelsUsed ++ uses L := by
  simp [uses]

@[simp] theorem uses_append (A B : List Line) : uses (A ++ B) = uses A ++ uses B := by
  simp [uses]

theorem mem_defs {L : List Line} {l : Lbl} : l ∈ defs L ↔ Line.label l ∈ L := by
  simp only [defs, List.mem_filterMap]
  constructor
  · rintro ⟨ln, h1, h2⟩
    cases ln <;> simp [lineDef] at h2
    subst h2; exact h1
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_uses {L : List Line} {l : Lbl} : l ∈ uses L ↔ ∃ ln ∈ L, l ∈ ln.labelsUsed := by
  simp [uses]

/-! ## `labelOffsets` succeeds on distinct labels -/

theorem labelOffsets_go_ok : ∀ (L : List Line) (off : Nat) (m : Std.HashMap Lbl Nat),
    (defs L).Nodup → (∀ l ∈ defs L, m.contains l = false) → ∃ m', labelOffsets.go L off m = .ok m'
  | [], _, m, _, _ => ⟨m, rfl⟩
  | ln :: L, off, m, hn, hm => by
    cases ln with
    | label l =>
      simp only [defs_cons, lineDef, Option.toList_some, List.singleton_append,
        List.nodup_cons] at hn
      have hl : m.contains l = false := hm l (by simp [lineDef])
      simp only [labelOffsets.go, hl, Bool.false_eq_true, ite_false]
      refine labelOffsets_go_ok L off (m.insert l off) hn.2 (fun x hx => ?_)
      rw [Std.HashMap.contains_insert]
      have hxl : (l == x) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hn.1 hx
      simp [hxl, hm x (by simp [lineDef, hx])]
    | ins i t =>
      simp only [labelOffsets.go]
      exact labelOffsets_go_ok L _ m (by simpa [lineDef] using hn)
        (fun x hx => hm x (by simp [lineDef, hx]))
    | word a b =>
      simp only [labelOffsets.go]
      exact labelOffsets_go_ok L _ m (by simpa [lineDef] using hn)
        (fun x hx => hm x (by simp [lineDef, hx]))

/-! ## Relaxation keeps the labels -/

theorem invertTo_used (c : Insn) (e : Lbl) (tr : Option Clif.TrapCode) :
    ∀ x ∈ (Line.ins (c.invertTo e) tr).labelsUsed,
      x ∈ (Line.ins c tr).labelsUsed ∨ x ∈ (Line.ins (.b e) none).labelsUsed := by
  intro x hx
  cases c <;> simp_all [Insn.invertTo, Line.labelsUsed, Insn.pcRelSpec?]

theorem relaxTarget_used {c : Insn} {t : Lbl} (h : c.relaxTarget? = some t) :
    t ∈ (Line.ins c none).labelsUsed := by
  have h1 : c.condTarget? = some t ∧ t ≠ .skip := by
    unfold Insn.relaxTarget? at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      exact ⟨‹_›, by simp⟩
  obtain ⟨hc, hs⟩ := h1
  cases c <;> simp only [Insn.condTarget?, reduceCtorEq] at hc <;> (try split at hc) <;>
    simp_all [Line.labelsUsed, Insn.pcRelSpec?]

theorem relaxable_some {ln : Line} {c : Insn} {t : Lbl} (h : ln.relaxable? = some (c, t)) :
    ln = .ins c none ∧ c.relaxTarget? = some t := by
  cases ln with
  | ins i tr =>
    cases tr with
    | none =>
      simp only [Line.relaxable?, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', h1, rfl, rfl⟩ := h
      exact ⟨rfl, h1⟩
    | some _ => simp [Line.relaxable?] at h
  | word => simp [Line.relaxable?] at h
  | label => simp [Line.relaxable?] at h

theorem relaxLine_spec (far : Lbl → Bool) (ln : Line) :
    defs (relaxLine far ln) = defs [ln] ∧ ∀ x ∈ uses (relaxLine far ln), x ∈ ln.labelsUsed := by
  unfold relaxLine
  split
  · rename_i c t hr
    obtain ⟨rfl, ht⟩ := relaxable_some hr
    split
    · refine ⟨by simp [lineDef], fun x hx => ?_⟩
      simp only [uses_cons, uses_nil, List.append_nil, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases invertTo_used c .skip none x hx with h | h
        · exact h
        · simp [Line.labelsUsed, Insn.pcRelSpec?] at h
      · have : x = t := by
          simp only [Line.labelsUsed, Insn.pcRelSpec?] at hx
          split at hx <;> simp_all
        subst this
        exact relaxTarget_used ht
    · exact ⟨rfl, fun x hx => by simpa using hx⟩
  · exact ⟨rfl, fun x hx => by simpa using hx⟩

theorem relaxLines_spec (far : Lbl → Bool) : ∀ L : List Line,
    defs (relaxLines far L) = defs L ∧ ∀ x ∈ uses (relaxLines far L), x ∈ uses L
  | [] => ⟨rfl, fun _ h => h⟩
  | ln :: L => by
    obtain ⟨h1, h2⟩ := relaxLine_spec far ln
    obtain ⟨ih1, ih2⟩ := relaxLines_spec far L
    have e : relaxLines far (ln :: L) = relaxLine far ln ++ relaxLines far L := by
      simp [relaxLines]
    rw [e, defs_append, h1, ih1, uses_cons]
    refine ⟨by simp, fun x hx => ?_⟩
    rw [uses_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact List.mem_append_left _ (h2 x hx)
    · exact List.mem_append_right _ (ih2 x hx)

/-! ## `fallthrough` keeps the labels -/

theorem ftStep_spec (ln : Line) (rest : List Line) :
    defs (ftStep ln rest[0]? rest[1]?).1 = defs ((ln :: rest).take (ftStep ln rest[0]? rest[1]?).2) ∧
      ∀ x ∈ uses (ftStep ln rest[0]? rest[1]?).1,
        x ∈ uses ((ln :: rest).take (ftStep ln rest[0]? rest[1]?).2) := by
  rcases rest with _ | ⟨a, _ | ⟨b, rest⟩⟩
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
  all_goals unfold ftStep
  all_goals constructor
  all_goals repeat' split
  all_goals simp_all [lineDef]
  exact fun x hx => invertTo_used _ _ none x hx

theorem ftList_spec : ∀ (n : Nat) (L : List Line), L.length ≤ n →
    defs (ftList L) = defs L ∧ ∀ x ∈ uses (ftList L), x ∈ uses L
  | _, [], _ => by simp [ftList]
  | 0, _ :: _, h => by simp at h
  | n + 1, ln :: rest, h => by
    rw [ftList_cons]
    obtain ⟨h1, h2⟩ := ftStep_spec ln rest
    have hp := (ftStep_pos ln rest[0]? rest[1]?).1
    generalize ftStep ln rest[0]? rest[1]? = st at *
    obtain ⟨out, k⟩ := st
    simp only at h1 h2 hp ⊢
    obtain ⟨ih1, ih2⟩ := ftList_spec n ((ln :: rest).drop k) (by simp at h ⊢; omega)
    have e := List.take_append_drop k (ln :: rest)
    refine ⟨by rw [defs_append, h1, ih1, ← defs_append, e], fun x hx => ?_⟩
    rw [← e, uses_append, List.mem_append]
    rw [uses_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact .inl (h2 x hx)
    · exact .inr (ih2 x hx)

/-! ## Chunks of emitted lines -/

/-- The deferred traps are `.trap 0, .trap 1, …` in order. -/
def TrapsOk (ps : PState) : Prop :=
  ps.traps.toList.map Prod.fst = (List.range ps.traps.size).map Lbl.trap

/-- Lines `ls` emitted from state `ps` to `ps'`, with block-label targets in `T` and defining
the block labels `B`: the counters only grow, the labels defined are distinct (block labels of
`B`, jump-table/loop labels of the counters' new range), and every label used is defined in
`ls`, a block label of `T` or a deferred trap. -/
structure Chunk (T B : List Label) (ps : PState) (ls : List Line) (ps' : PState) : Prop where
  traps : TrapsOk ps → TrapsOk ps'
  tsz : ps.traps.size ≤ ps'.traps.size
  jt : ps.jt ≤ ps'.jt
  al : ps.aloop ≤ ps'.aloop
  nodup : (defs ls).Nodup
  defs_in : ∀ x ∈ defs ls, (∃ l ∈ B, x = .block l) ∨ (∃ n, x = .jt n ∧ ps.jt ≤ n ∧ n < ps'.jt) ∨
    (∃ n, x = .loop n ∧ ps.aloop ≤ n ∧ n < ps'.aloop)
  blocks : ∀ l ∈ B, Lbl.block l ∈ defs ls
  uses_in : ∀ x ∈ uses ls, x ∈ defs ls ∨ (∃ l ∈ T, x = .block l) ∨
    (∃ n, x = .trap n ∧ n < ps'.traps.size)

theorem Chunk.append {T B1 B2 : List Label} {ps ps1 ps2 : PState} {l1 l2 : List Line}
    (h1 : Chunk T B1 ps l1 ps1) (h2 : Chunk T B2 ps1 l2 ps2) (hd : ∀ l ∈ B1, l ∉ B2) :
    Chunk T (B1 ++ B2) ps (l1 ++ l2) ps2 where
  traps h := h2.traps (h1.traps h)
  tsz := Nat.le_trans h1.tsz h2.tsz
  jt := Nat.le_trans h1.jt h2.jt
  al := Nat.le_trans h1.al h2.al
  nodup := by
    rw [defs_append, List.nodup_append]
    refine ⟨h1.nodup, h2.nodup, fun x hx y hy hxy => ?_⟩
    subst hxy
    have := h1.jt; have := h1.al
    rcases h1.defs_in x hx with ⟨l, hl, rfl⟩ | ⟨n, rfl, -, hn⟩ | ⟨n, rfl, -, hn⟩ <;>
    rcases h2.defs_in _ hy with ⟨l', hl', he⟩ | ⟨n', he, hn', -⟩ | ⟨n', he, hn', -⟩ <;>
    simp only [Lbl.block.injEq, Lbl.jt.injEq, Lbl.loop.injEq, reduceCtorEq] at he
    · subst he; exact hd _ hl hl'
    · omega
    · omega
  defs_in x hx := by
    rw [defs_append, List.mem_append] at hx
    rcases hx with hx | hx
    · rcases h1.defs_in x hx with ⟨l, hl, rfl⟩ | ⟨n, rfl, h3, h4⟩ | ⟨n, rfl, h3, h4⟩
      · exact .inl ⟨l, List.mem_append_left _ hl, rfl⟩
      · exact .inr (.inl ⟨n, rfl, h3, by have := h2.jt; omega⟩)
      · exact .inr (.inr ⟨n, rfl, h3, by have := h2.al; omega⟩)
    · rcases h2.defs_in x hx with ⟨l, hl, rfl⟩ | ⟨n, rfl, h3, h4⟩ | ⟨n, rfl, h3, h4⟩
      · exact .inl ⟨l, List.mem_append_right _ hl, rfl⟩
      · exact .inr (.inl ⟨n, rfl, by have := h1.jt; omega, h4⟩)
      · exact .inr (.inr ⟨n, rfl, by have := h1.al; omega, h4⟩)
  blocks l hl := by
    rw [defs_append, List.mem_append]
    rcases List.mem_append.mp hl with hl | hl
    · exact .inl (h1.blocks l hl)
    · exact .inr (h2.blocks l hl)
  uses_in x hx := by
    rw [uses_append, List.mem_append] at hx
    rw [defs_append, List.mem_append]
    rcases hx with hx | hx
    · rcases h1.uses_in x hx with h | h | ⟨n, rfl, hn⟩
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨n, rfl, by have := h2.tsz; omega⟩)
    · rcases h2.uses_in x hx with h | h | h
      · exact .inl (.inr h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)

theorem Chunk.mono {T T' B : List Label} {ps ps' : PState} {ls : List Line}
    (h : Chunk T B ps ls ps') (hT : ∀ l ∈ T, l ∈ T') : Chunk T' B ps ls ps' := by
  refine ⟨h.traps, h.tsz, h.jt, h.al, h.nodup, h.defs_in, h.blocks, fun x hx => ?_⟩
  rcases h.uses_in x hx with h1 | ⟨l, hl, rfl⟩ | h1
  · exact .inl h1
  · exact .inr (.inl ⟨l, hT l hl, rfl⟩)
  · exact .inr (.inr h1)

/-- Lines without labels and label operands. -/
def Plain (L : List Line) : Prop := ∀ ln ∈ L, lineDef ln = none ∧ ln.labelsUsed = []

theorem Plain.noDefs {L : List Line} (h : Plain L) : defs L = [] := by
  simp only [defs, List.filterMap_eq_nil_iff]; exact fun ln hl => (h ln hl).1

theorem Plain.noUses {L : List Line} (h : Plain L) : uses L = [] := by
  simp only [uses, List.flatMap_eq_nil_iff]; exact fun ln hl => (h ln hl).2

theorem plain_chunk {T : List Label} {ps : PState} {L : List Line} (h : Plain L) :
    Chunk T [] ps L ps where
  traps := id
  tsz := Nat.le_refl _
  jt := Nat.le_refl _
  al := Nat.le_refl _
  nodup := by rw [h.noDefs]; exact List.nodup_nil
  defs_in x hx := by rw [h.noDefs] at hx; cases hx
  blocks l hl := by cases hl
  uses_in x hx := by rw [h.noUses] at hx; cases hx

theorem plain_append {A B : List Line} (ha : Plain A) (hb : Plain B) : Plain (A ++ B) := by
  intro ln hl
  rcases List.mem_append.mp hl with hl | hl
  · exact ha ln hl
  · exact hb ln hl

theorem plain_nil : Plain [] := fun _ h => by cases h

theorem plain_ins (i : Insn) (t : Option Clif.TrapCode) (hi : i.pcRelSpec? = none) :
    Plain [.ins i t] := by
  intro ln hl
  simp only [List.mem_singleton] at hl
  subst hl
  simp [lineDef, Line.labelsUsed, hi]

theorem loadConst64_plain (rd : Reg) (v : Nat) : Plain (loadConst64 rd v) := by
  intro ln hln
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at hln
  rcases hln with rfl | ⟨j, -, hj⟩
  · simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]
  · split at hj
    · simp only [Option.some.injEq] at hj
      subst hj
      simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]
    · cases hj

theorem memFinalize_plain {c : FnCtx} {m : AMode} {b : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m b = .ok (pre, m')) : Plain pre := by
  unfold memFinalize at h
  split at h
  all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals (repeat' split at h) <;> (try simp only [Prod.mk.injEq] at h) <;> obtain ⟨rfl, -⟩ := h <;>
    first | exact plain_nil | exact loadConst64_plain _ _

theorem chunk_same {T : List Label} {ps : PState} {ls : List Line} (hd : defs ls = [])
    (hu : ∀ x ∈ uses ls, ∃ l ∈ T, x = .block l) : Chunk T [] ps ls ps where
  traps := id
  tsz := Nat.le_refl _
  jt := Nat.le_refl _
  al := Nat.le_refl _
  nodup := by rw [hd]; exact List.nodup_nil
  defs_in x hx := by rw [hd] at hx; cases hx
  blocks l hl := by cases hl
  uses_in x hx := .inr (.inl (hu x hx))

theorem insn_used (k : CondBrKind) (t : Lbl) (tr : Option Clif.TrapCode) (ht : t ≠ .skip) :
    (Line.ins (k.insn t) tr).labelsUsed = [t] := by
  cases k <;> simp [CondBrKind.insn, Line.labelsUsed, Insn.pcRelSpec?, ht]

theorem rmwLoopCmp_pc (op : AtomicRmwLoopOp) (bits : Nat) : (rmwLoopCmp op bits).pcRelSpec? = none := by
  unfold rmwLoopCmp; split <;> rfl

theorem rmwLoopMid_pc (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, i.pcRelSpec? = none := by
  intro i hi
  cases op <;> simp only [rmwLoopMid, rmwLoopSext, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hi
  all_goals first
    | (rcases hi with rfl | rfl <;> first | rfl | exact rmwLoopCmp_pc _ _)
    | (subst hi; rfl)
    | (rcases hi with hi | rfl | rfl
       · split at hi <;> simp at hi <;> subst hi <;> rfl
       · exact rmwLoopCmp_pc _ _
       · rfl)

theorem rmwLoopBody_plain (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    Plain (rmwLoopBody bits op fl) := by
  intro ln hl
  simp only [rmwLoopBody, List.mem_append, List.mem_singleton, List.mem_map] at hl
  rcases hl with (rfl | ⟨i, hi, rfl⟩) | rfl
  · simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]
  · simp [lineDef, Line.labelsUsed, rmwLoopMid_pc op bits i hi]
  · simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]

theorem casLoopCmp_pc (bits : Nat) : (casLoopCmp bits).pcRelSpec? = none := by
  unfold casLoopCmp; split <;> rfl

theorem casLoopHead_plain (bits : Nat) (fl : Clif.MemFlags) : Plain (casLoopHead bits fl) := by
  intro ln hl
  simp only [casLoopHead, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]
  · simp [lineDef, Line.labelsUsed, casLoopCmp_pc]

@[simp] theorem defs_words (ts : List Label) (j : Lbl) :
    defs (ts.map fun l => Line.word (.block l) j) = [] := by
  induction ts <;> simp_all [lineDef]

theorem lines_chunk {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : Chunk m.targets [] ps ls ps' := by
  cases m
  all_goals simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h
       refine plain_chunk ?_
       simp [Plain, lineDef, Line.labelsUsed, Insn.pcRelSpec?]
       done)
    | (obtain ⟨rfl, rfl⟩ := h
       refine plain_chunk ?_
       split <;> simp [Plain, lineDef, Line.labelsUsed, Insn.pcRelSpec?]
       done)
    | skip
  case aluRRImmLogic | aluRRImmShift | aluRRRShift | call | extend =>
    repeat' split at h
    all_goals simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := h; exact plain_chunk (plain_ins _ _ rfl))
      | cases h
  case args | rets => cases h
  case load | store =>
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hm
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact plain_chunk (plain_append (memFinalize_plain hm) (plain_ins _ _ rfl))
  case loadAddr =>
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hm
      obtain ⟨pre, mm⟩ := r
      split at h
      all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq] at h)
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := h
           refine plain_chunk (plain_append (memFinalize_plain hm) ?_)
           try simp only [MInst.lines.addOff]
           repeat' split
           all_goals first | exact plain_nil | exact plain_ins _ _ rfl)
        | cases h
  case elfTlsGetAddr =>
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine plain_chunk ?_
      simp [Plain, lineDef, Line.labelsUsed, Insn.pcRelSpec?]
  case jump =>
    obtain ⟨rfl, rfl⟩ := h
    refine chunk_same (by simp [lineDef]) fun x hx => ?_
    simp [Line.labelsUsed, Insn.pcRelSpec?] at hx
    exact ⟨_, by simp [MInst.targets], hx⟩
  case condBr | testBitAndBranch =>
    obtain ⟨rfl, rfl⟩ := h
    refine chunk_same (by simp [lineDef]) fun x hx => ?_
    simp only [uses_cons, uses_nil, List.append_nil] at hx
    try rw [insn_used _ _ _ (by simp)] at hx
    simp [Line.labelsUsed, Insn.pcRelSpec?] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, by simp [MInst.targets], rfl⟩
  case tryCall info ti =>
    obtain ⟨⟨dest, us, ds⟩, rfl⟩ : ∃ d, info = d := ⟨_, rfl⟩
    obtain ⟨rfl, rfl⟩ := h
    refine chunk_same (by cases dest <;> simp [lineDef]) fun x hx => ?_
    cases dest <;> simp [Line.labelsUsed, Insn.pcRelSpec?] at hx <;> subst hx <;>
      exact ⟨_, by simp [MInst.targets], rfl⟩
  case trapIf =>
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun ht => ?_, by simp, Nat.le_refl _, Nat.le_refl _, by simp [lineDef],
      by simp [lineDef], (fun _ h => nomatch h), fun x hx => ?_⟩
    · simp only [TrapsOk] at ht ⊢
      simp [ht, List.range_succ]
    · simp [insn_used] at hx
      subst hx
      exact .inr (.inr ⟨_, rfl, by simp⟩)
  case jtSequence =>
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨id, Nat.le_refl _, by simp, Nat.le_refl _, by simp [lineDef], ?_,
      (fun _ h => nomatch h), fun x hx => ?_⟩
    · intro x hx
      simp [lineDef] at hx
      exact .inr (.inl ⟨_, hx, Nat.le_refl _, by simp⟩)
    · rw [uses_append, List.mem_append] at hx
      rcases hx with hx | hx
      · simp [Line.labelsUsed, Insn.pcRelSpec?] at hx
        rcases hx with rfl | rfl
        · exact .inr (.inl ⟨_, by simp [MInst.targets], rfl⟩)
        · exact .inl (by simp [lineDef])
      · rw [mem_uses] at hx
        obtain ⟨ln, hln, hx⟩ := hx
        simp only [List.mem_map] at hln
        obtain ⟨l, hl, rfl⟩ := hln
        simp only [Line.labelsUsed, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact .inr (.inl ⟨l, by simp [MInst.targets, hl], rfl⟩)
        · exact .inl (by simp [lineDef])
  case atomicRmwLoop =>
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb := rmwLoopBody_plain
      refine ⟨id, Nat.le_refl _, Nat.le_refl _, by simp, ?_, ?_, (fun _ h => nomatch h), fun x hx => ?_⟩
      · simp [rmwLoopLines, lineDef, (hb _ _ _).noDefs]
      · intro x hx
        simp [rmwLoopLines, lineDef, (hb _ _ _).noDefs] at hx
        exact .inr (.inr ⟨_, hx, Nat.le_refl _, by simp⟩)
      · simp [rmwLoopLines, (hb _ _ _).noUses, Line.labelsUsed, Insn.pcRelSpec?] at hx
        exact .inl (by simp [rmwLoopLines, lineDef, (hb _ _ _).noDefs, hx])
  case atomicCasLoop =>
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb := casLoopHead_plain
      refine ⟨id, Nat.le_refl _, Nat.le_refl _, by simp, ?_, ?_, (fun _ h => nomatch h), fun x hx => ?_⟩
      · simp [casLoopLines, lineDef, (hb _ _).noDefs]
      · intro x hx
        simp [casLoopLines, lineDef, (hb _ _).noDefs] at hx
        rcases hx with rfl | rfl
        · exact .inr (.inr ⟨_, rfl, Nat.le_refl _, by simp⟩)
        · exact .inr (.inr ⟨_, rfl, by simp, by simp⟩)
      · simp [casLoopLines, (hb _ _).noUses, Line.labelsUsed, Insn.pcRelSpec?] at hx
        refine .inl ?_
        rcases hx with rfl | rfl <;> simp [casLoopLines, lineDef, (hb _ _).noDefs]

/-! ## Blocks -/

theorem prologueLines_plain (size : Nat) : Plain (prologueLines size) := by
  unfold prologueLines
  refine plain_append (by simp [Plain, lineDef, Line.labelsUsed, Insn.pcRelSpec?]) ?_
  split
  · exact plain_nil
  · split
    · exact plain_ins _ _ rfl
    · exact plain_append (loadConst64_plain _ _) (plain_ins _ _ rfl)

theorem epilogueLines_plain (size : Nat) : Plain (epilogueLines size) := by
  unfold epilogueLines
  refine plain_append ?_ (by simp [Plain, lineDef, Line.labelsUsed, Insn.pcRelSpec?])
  split
  · exact plain_nil
  · split
    · exact plain_ins _ _ rfl
    · exact plain_append (loadConst64_plain _ _) (plain_ins _ _ rfl)

theorem ainst_chunk {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    {T : List Label} (h : ainstLines c af a ps = .ok (ls, ps'))
    (ht : ∀ m, a = .inst m → ∀ l ∈ m.targets, l ∈ T) : Chunk T [] ps ls ps' := by
  cases a with
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split
    · exact plain_chunk (prologueLines_plain _)
    · exact plain_chunk plain_nil
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split
    · exact plain_chunk (epilogueLines_plain _)
    · exact plain_chunk (plain_ins _ _ rfl)
  | inst m => exact (lines_chunk h).mono (ht m rfl)

theorem code_chunk {c : FnCtx} {af : AFunc} {T : List Label} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') →
      (∀ m, AInst.inst m ∈ code → ∀ l ∈ m.targets, l ∈ T) → Chunk T [] ps ls ps'
  | [], ps, ps', ls, h, _ => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact plain_chunk plain_nil
  | a :: as, ps, ps', ls, h, ht => by
    simp only [codeLinesE, bind, Except.bind] at h
    cases h1 : ainstLines c af a ps with
    | error e => rw [h1] at h; cases h
    | ok r =>
      rw [h1] at h
      obtain ⟨l1, ps1⟩ := r
      simp only at h
      cases h2 : codeLinesE c af as ps1 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        rw [h2] at h
        obtain ⟨l2, ps2⟩ := r2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Chunk.append
          (ainst_chunk h1 fun m hm l hl => ht m (by simp [hm]) l hl)
          (code_chunk as ps1 ps2 l2 h2 fun m hm l hl => ht m (by simp [hm]) l hl)
          (fun _ h => nomatch h)

theorem blocks_chunk {c : FnCtx} {af : AFunc} {T : List Label} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (body : List Line),
      blocksLinesE c af bs ps = .ok (body, ps') → (bs.map (·.1)).Nodup →
      (∀ p ∈ bs, ∀ m, AInst.inst m ∈ p.2.toList → ∀ l ∈ m.targets, l ∈ T) →
      Chunk T (bs.map (·.1)) ps body ps'
  | [], ps, ps', body, h, _, _ => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact plain_chunk plain_nil
  | (l', code) :: bs, ps, ps', body, h, hn, ht => by
    simp only [blocksLinesE, bind, Except.bind] at h
    cases h1 : codeLinesE c af code.toList ps with
    | error e => rw [h1] at h; cases h
    | ok r =>
      rw [h1] at h
      obtain ⟨l1, ps1⟩ := r
      simp only at h
      cases h2 : blocksLinesE c af bs ps1 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        rw [h2] at h
        obtain ⟨l2, ps2⟩ := r2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.map_cons, List.nodup_cons] at hn
        have hlab : Chunk T [l'] ps [.label (.block l')] ps :=
          ⟨id, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by simp [lineDef],
            fun x hx => .inl ⟨l', by simp, by simpa [lineDef] using hx⟩,
            fun x hx => by simp at hx; simp [lineDef, hx],
            fun x hx => by simp [Line.labelsUsed] at hx⟩
        have hcode := code_chunk (T := T) code.toList ps ps1 l1 h1
          (fun m hm l hl => ht (l', code) (by simp) m hm l hl)
        have hrest := blocks_chunk bs ps1 ps2 l2 h2 hn.2
          (fun p hp m hm l hl => ht p (by simp [hp]) m hm l hl)
        have := Chunk.append (Chunk.append hlab hcode (fun _ _ h => nomatch h)) hrest
          (fun x hx => by simp at hx; subst hx; exact hn.1)
        simpa using this

/-! ## `emitFunc`'s labels -/

theorem trapLines_spec (ts : List (Lbl × Clif.TrapCode)) :
    defs (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]) =
        ts.map Prod.fst ∧
      uses (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]) = [] := by
  induction ts with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
    simp only [List.flatMap_cons, defs_append, uses_append, ih.1, ih.2]
    simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]

/-- **The labels of `emitFunc`'s code**, from the allocated function: if its blocks' labels are
distinct and every branch target of its instructions is one of them, every label is defined once
and every label operand names a defined label. -/
theorem emitFunc_labels_of {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa)
    (hn : (af.blocks.toList.map (·.1)).Nodup)
    (ht : ∀ p ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ p.2.toList → ∀ l ∈ m.targets,
      l ∈ af.blocks.toList.map (·.1)) :
    (∃ m, labelOffsets fa.lines = .ok m) ∧
      (∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList) := by
  obtain ⟨pre, hpre, hlines, -, -⟩ := emitFunc_unfold he
  obtain ⟨body, ps, hb, rfl⟩ := emitPre_ok hpre
  have hc := blocks_chunk (T := af.blocks.toList.map (·.1)) _ _ _ _ hb hn ht
  have hT : TrapsOk ps := hc.traps (by simp [TrapsOk])
  obtain ⟨hft1, hft2⟩ := ftList_spec _ body (Nat.le_refl _)
  obtain ⟨htr1, htr2⟩ := trapLines_spec ps.traps.toList
  generalize hP : (ftList body ++ ps.traps.toList.flatMap
    fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]) = P at hlines
  obtain ⟨hr1, hr2⟩ := relaxLines_spec (relaxOf P) P
  have hL : fa.lines.toList = relaxLines (relaxOf P) P := by rw [hlines, List.toList_toArray]
  rw [← hL] at hr1 hr2
  rw [← hP, defs_append, hft1, htr1, hT] at hr1
  rw [← hP, uses_append, htr2, List.append_nil] at hr2
  constructor
  · refine labelOffsets_go_ok _ 0 {} ?_ (fun l _ => by simp)
    rw [hr1, List.nodup_append]
    refine ⟨hc.nodup, List.Pairwise.map Lbl.trap (fun _ _ h e => h (Lbl.trap.inj e)) List.nodup_range, fun x hx y hy hxy => ?_⟩
    subst hxy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨n, -, rfl⟩ := hy
    rcases hc.defs_in _ hx with ⟨_, _, h⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  · intro ln hln l hl
    rw [← mem_defs, hr1, List.mem_append]
    rcases hc.uses_in l (hft2 l (hr2 l (mem_uses.2 ⟨ln, hln, hl⟩))) with h | ⟨b, hb, rfl⟩ | ⟨n, rfl, hn⟩
    · exact .inl h
    · exact .inl (hc.blocks b hb)
    · exact .inr (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)

/-! ## Branch targets of the allocated code -/

/-- `x`'s results satisfy `P`. -/
def Post {α : Type} (P : α → Prop) (x : StateT Nat (Except String) α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → P a

theorem post_pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    Post P (pure a : StateT Nat (Except String) α) := by
  intro s a' s' h'
  cases h'
  exact h

theorem post_bind {α β : Type} {P : β → Prop} {x : StateT Nat (Except String) α}
    {g : α → StateT Nat (Except String) β} (h : ∀ a, Post P (g a)) : Post P (x >>= g) := by
  intro s b s' h'
  rw [StateT.run_bind] at h'
  cases hx : x.run s with
  | error e => rw [hx] at h'; cases h'
  | ok p => rw [hx] at h'; exact h p.1 p.2 b s' h'

theorem visit_targets (f : OpSpec → Reg → StateT Nat (Except String) Reg) (i : MInst) :
    Post (fun r => r.targets = i.targets) (MInst.visitOperands f i) := by
  cases i <;> simp only [MInst.visitOperands] <;>
    repeat' (first | exact post_pure rfl | refine post_bind fun _ => ?_ | split)

/-- Substituting an allocation keeps the branch targets. -/
theorem assign_targets {i i' : MInst} {regs : Array Reg} (h : i.assign regs = .ok i') :
    i'.targets = i.targets := by
  rw [Backend.Proof.assign_eq] at h
  simp only [bind, Except.bind] at h
  cases hr : (MInst.visitOperands (Backend.Proof.putOp regs) i).run 0 with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    obtain ⟨i1, k⟩ := p
    simp only at h
    split at h
    · cases h
    · cases h
      exact visit_targets _ i 0 i' k hr

theorem moveInsts_targets {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : ∀ m, AInst.inst m ∈ l → m.targets = [] := by
  have hst : ∀ cls r off, ∀ m ∈ slotStoreAt cls r off, m.targets = [] := by
    intro cls r off m hm
    unfold slotStoreAt spAddrX16 at hm
    cases cls <;> split at hm <;> simp [slotStore] at hm <;>
      (try rcases hm with rfl | ⟨_, _, -, rfl⟩ | rfl | rfl) <;> (try subst hm) <;> rfl
  have hld : ∀ cls r off, ∀ m ∈ slotLoadAt cls r off, m.targets = [] := by
    intro cls r off m hm
    unfold slotLoadAt spAddrX16 at hm
    cases cls <;> split at hm <;> simp [slotLoad] at hm <;>
      (try rcases hm with rfl | ⟨_, _, -, rfl⟩ | rfl | rfl) <;> (try subst hm) <;> rfl
  intro m hm
  unfold RAFrame.moveInsts at h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm; rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [List.mem_map, List.mem_append, AInst.inst.injEq] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      rcases hm' with hm' | hm'
      · exact hst _ _ _ _ hm'
      · exact hld _ _ _ _ hm'
  all_goals (try simp only [bind, Except.bind] at h)
  all_goals first
    | cases h
    | (split at h
       · cases h
       · simp only [pure, Except.pure, Except.ok.injEq] at h
         subst h
         simp only [List.mem_map, AInst.inst.injEq] at hm
         obtain ⟨m', hm', rfl⟩ := hm
         first | exact hst _ _ _ _ hm' | exact hld _ _ _ _ hm')

/-- Every branch target of an item list's code is one of an instruction of the block. -/
theorem itemsCode_targets {fr : RAFrame} {vb : VBlock} :
    ∀ (its : List RItem) (code : List AInst), itemsCode fr vb its = .ok code →
      ∀ m, AInst.inst m ∈ code → ∀ l ∈ m.targets, ∃ i ∈ vb.insts.toList, l ∈ i.targets
  | [], code, h, m, hm => by
    simp only [itemsCode, pure, Except.pure, Except.ok.injEq] at h
    subst h; cases hm
  | it :: its, code, h, m, hm => by
    obtain ⟨c1, c2, h1, h2, rfl⟩ := Backend.Proof.itemsCode_cons h
    rcases List.mem_append.mp hm with hm | hm
    · cases it with
      | move src dst =>
        rw [Backend.Proof.itemCode_move] at h1
        intro l hl
        rw [moveInsts_targets h1 m hm] at hl
        cases hl
      | op k allocs =>
        obtain ⟨regs, i, i', -, hi, hasg, hc⟩ := Backend.Proof.itemCode_op h1
        intro l hl
        refine ⟨i, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi), ?_⟩
        rcases hc with ⟨rfl, -, -⟩ | ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩
        · simp only [List.mem_singleton, AInst.inst.injEq] at hm
          subst hm
          rwa [← assign_targets hasg]
        · cases hm
        · simp at hm
    · exact itemsCode_targets its c2 h2 m hm
end E2E.EmitLabels

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver EmitLabels

/-- `prepare`'s output has distinct block labels (on `PrepDomain` input). -/
theorem prepare_labels_nodup {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc) :
    (vcp.blocks.toList.map VBlock.label).Nodup := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨-, -, -, -, hn2, hR, hRn, -, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  exact Prep.lbls3 hR hn2 hRn

/-- **Labels of the lowered code** for any allocation `rf` covering the blocks: with distinct
block labels and `branchTargetsOkB`, `emitFunc`'s labels are defined once and every label operand
names a defined label. -/
theorem emitFunc_labels_lowerRFunc {vcp : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (hn : (vcp.blocks.toList.map VBlock.label).Nodup) (htg : branchTargetsOkB vcp = true)
    (hrf : vcp.blocks.size ≤ rf.blocks.size)
    (ha : lowerRFunc vcp rf = .ok af) (he : emitFunc k af = .ok fa) :
    (∃ m, labelOffsets fa.lines = .ok m) ∧
      (∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList) := by
  obtain ⟨⟨-, -, hafs, hblk⟩, -, -⟩ := lowerRFunc_ok ha
  have hsz : af.blocks.size = vcp.blocks.size := by
    rw [hafs, Array.size_zip]; omega
  -- block `n` of `af`
  have hget : ∀ n (hn : n < af.blocks.size), ∃ code, itemsCode (RAFrame.compute vcp rf)
      vcp.blocks[n] (rf.blocks[n]'(by omega)).toList = .ok code ∧
      af.blocks[n] = (vcp.blocks[n].label,
        ((if n = 0 then [AInst.prologue] else []) ++ code).toArray) := by
    intro n hn
    obtain ⟨code, hc, he⟩ := hblk n vcp.blocks[n] (rf.blocks[n]'(by omega))
      (Array.getElem?_eq_getElem (by omega)) (Array.getElem?_eq_getElem (by omega))
    exact ⟨code, hc, Option.some.inj (by rw [← Array.getElem?_eq_getElem hn]; exact he)⟩
  have hlab : af.blocks.toList.map (·.1) = vcp.blocks.toList.map VBlock.label := by
    apply List.ext_getElem
    · simp [hsz]
    · intro n h1 _
      simp only [List.length_map, Array.length_toList] at h1
      simp only [List.getElem_map, Array.getElem_toList]
      rw [(hget n h1).choose_spec.2]
  refine emitFunc_labels_of he (hlab ▸ hn) (fun p hp m hm l hl => ?_)
  obtain ⟨n, hnl, rfl⟩ := List.getElem_of_mem hp
  simp only [Array.length_toList] at hnl
  obtain ⟨code, hc, hpe⟩ := hget n hnl
  simp only [Array.getElem_toList, hpe, List.toList_toArray] at hm
  have hm' : AInst.inst m ∈ code := by
    rcases List.mem_append.mp hm with h | h
    · split at h <;> simp at h
    · exact h
  obtain ⟨i, hi, hli⟩ := itemsCode_targets _ code hc m hm' l hl
  rw [hlab]
  simp only [branchTargetsOkB, Array.all_eq_true, List.all_eq_true, Array.any_eq_true,
    beq_iff_eq] at htg
  have hnv : n < vcp.blocks.size := by omega
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hi
  simp only [Array.length_toList] at hq
  obtain ⟨j, hj, e⟩ := htg n hnv q hq l (by simpa using hli)
  exact List.mem_map.2 ⟨vcp.blocks[j], by simp, e⟩

theorem spillAlloc_size (vc : VCode) : (spillAlloc vc).blocks.size = vc.blocks.size := by
  unfold spillAlloc
  split <;> exact Array.size_mapIdx ..

/-- **The labels of the spill allocation's code** (V6b): for an in-scope function whose prepared
VCode branches only to its blocks (`branchTargetsOkB`), the code `emitFunc` produces from the spill
allocation defines every label once (`labelOffsets` succeeds) and every label operand names a
defined label: the first two premises of `emitFunc_layout_total`. -/
theorem emitFunc_spill_labels {f : Clif.Function} {vc vcp : VCode} {af : AFunc} {k : Nat}
    {fa : FnAsm} (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) (htg : branchTargetsOkB vcp = true)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) (he : emitFunc k af = .ok fa) :
    (∃ m, labelOffsets fa.lines = .ok m) ∧
      (∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList) :=
  emitFunc_labels_lowerRFunc
    (prepare_labels_nodup hp (prepDomain_of_lower (lowerScope_of hs) hl (lowerScope_of hs).nonempty))
    htg (Nat.le_of_eq (spillAlloc_size vcp).symm) ha he

end E2E

