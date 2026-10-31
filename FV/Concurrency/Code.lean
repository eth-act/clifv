import FV.Backend.Asm
import FV.Concurrency.Armv8

/-!
# The mapping table is the table of the emitted code (T2b, #300)

Each `Backend.Insn` that accesses memory gets the Arm event kind of `FV/Concurrency/Armv8.lean`
(`Insn.akind?`): plain loads/stores (`ldr*`/`str*`, `ldp`/`stp`, the FP forms, the GOT and TLSDESC
loads, literal loads), `ldar` (`acqR`), `stlr` (`relW`), `ldaxr` (`acqXR`), `stlxr` (`relXW`) and
`dmb ish` (`dmb`). `MInst.lines_kinds` computes the kinds of the lines `MInst.lines` emits for every
allocated instruction (`MInst.akinds`):

* `loadAcquire` (`atomic_load`) ↦ `[acqR]`, `storeRelease` (`atomic_store`) ↦ `[relW]`,
  `fence` ↦ `[dmb]`;
* `atomicRmwLoop` (`atomic_rmw`) and `atomicCasLoop` (`atomic_cas`) ↦ `[acqXR, relXW]`: one
  `ldaxr` and one `stlxr`, with no other memory access between them (the `po`-adjacency of an
  `rmw` pair, `Exec.Wf.rmw_imm`), at the same size and address register x25
  (`rmwLoopLines_mem`, `casLoopLines_mem`);
* the other memory instructions ↦ one plain kind; everything else ↦ `[]`.

So acquire, release, exclusive and barrier events come only from CLIF atomics and `fence`, and with
the kinds of `Mapping.Maps`. The CLIF → `MInst` step (the ISLE root rules: `atomic_load` → `ldar`,
…) is proven in `FV/Backend/Proof/IselAtomic.lean`. Prologue, epilogue and branch relaxation
emit plain or no memory events (`prologueLines_kinds`, `epilogueLines_kinds`, `relaxLines_kinds`).
-/

namespace Concurrency.Code

open Backend

/-- The memory-event kind of an instruction (`none`: no memory event of this code). -/
def insnKind : Insn → Option AKind
  | .load .. | .ldp .. | .fpuLoad .. | .fpuLoadP .. | .ldrGotLo12 .. | .ldrTlsDescLo12 ..
  | .fpuLoadLit .. => some .plainR
  | .store .. | .stp .. | .fpuStore .. | .fpuStoreP .. => some .plainW
  | .ldar .. => some .acqR
  | .stlr .. => some .relW
  | .ldaxr .. => some .acqXR
  | .stlxr .. => some .relXW
  | .dmbish => some .dmb
  | _ => none

/-- The memory-event kind of a line. -/
def lineKind : Line → Option AKind
  | .ins i _ => insnKind i
  | _ => none

/-- The memory-event kinds of a line list, in program order. -/
def kinds (ls : List Line) : List AKind := ls.filterMap lineKind

/-- The memory instructions of a line list, in program order. -/
def memInsns (ls : List Line) : List Insn :=
  ls.filterMap fun l => match l with
    | .ins i _ => if (insnKind i).isSome then some i else none
    | _ => none

/-- The memory-event kinds of an allocated instruction's code. -/
def akinds : MInst → List AKind
  | .load .. | .fpuLoad .. | .jtSequence .. | .loadExtNameGot .. | .elfTlsGetAddr .. => [.plainR]
  | .store .. | .fpuStore .. => [.plainW]
  | .loadAcquire .. => [.acqR]
  | .storeRelease .. => [.relW]
  | .atomicRmwLoop .. | .atomicCasLoop .. => [.acqXR, .relXW]
  | .fence => [.dmb]
  | _ => []

theorem kinds_append (a b : List Line) : kinds (a ++ b) = kinds a ++ kinds b :=
  List.filterMap_append

theorem kinds_loadConst64 (rd : Reg) (v : Nat) : kinds (loadConst64 rd v) = [] := by
  unfold kinds loadConst64
  rw [List.filterMap_eq_nil_iff]
  intro l hl
  simp only [List.mem_cons, List.mem_filterMap, List.mem_range] at hl
  rcases hl with rfl | ⟨j, -, hj⟩
  · rfl
  · split at hj
    · cases hj; rfl
    · cases hj

theorem kinds_memFinalize {c : FnCtx} {m : AMode} {n : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m n = .ok (pre, m')) : kinds pre = [] := by
  unfold memFinalize at h
  have fin : ∀ (base : Reg) (off : Int) (p : List Line) (q : AMode),
      (match simm9? off with
        | some s => (([] : List Line), AMode.unscaled base s)
        | none => match uimm12Scaled? off n with
          | some o => ([], .unsignedOffset base o)
          | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (p, q) →
      kinds p = [] := by
    intro base off p q hpq
    split at hpq
    · cases hpq; rfl
    · split at hpq
      · cases hpq; rfl
      · cases hpq; exact kinds_loadConst64 _ _
  cases m <;> simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
  all_goals first
    | (cases h; rfl)
    | exact fin _ _ _ _ h

theorem insnKind_condBr (k : CondBrKind) (t : Lbl) : insnKind (k.insn t) = none := by
  cases k <;> rfl

theorem kinds_addOff (rd rn : Reg) (off : Int) : kinds (MInst.lines.addOff rd rn off) = [] := by
  unfold MInst.lines.addOff
  split
  · split <;> rfl
  · split <;> rfl

theorem insnKind_rmwLoopCmp (op : AtomicRmwLoopOp) (bits : Nat) :
    insnKind (rmwLoopCmp op bits) = none := by
  unfold rmwLoopCmp; split <;> rfl

theorem insnKind_casLoopCmp (bits : Nat) : insnKind (casLoopCmp bits) = none := by
  unfold casLoopCmp; split <;> rfl

theorem insnKind_rmwLoopSext (bits : Nat) : ∀ i ∈ rmwLoopSext bits, insnKind i = none := by
  unfold rmwLoopSext; split <;> simp [insnKind]

theorem insnKind_rmwLoopMid (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, insnKind i = none := by
  intro i hi
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hi
  all_goals
    rcases hi with h | h | h <;>
    first
      | rfl
      | exact insnKind_rmwLoopCmp _ _
      | (subst h; first | rfl | exact insnKind_rmwLoopCmp _ _)
      | exact insnKind_rmwLoopSext _ _ h

theorem kinds_rmwLoopMid (op : AtomicRmwLoopOp) (bits : Nat) :
    kinds ((rmwLoopMid op bits).map fun i => .ins i) = [] := by
  rw [kinds, List.filterMap_map, List.filterMap_eq_nil_iff]
  intro i hi
  simp [Function.comp, lineKind, insnKind_rmwLoopMid op bits i hi]

theorem rmwLoopLines_eq (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) :
    rmwLoopLines bits op fl l = [.label l, .ins (.ldaxr bits (.x 27) (.x 25)) fl.trapCode] ++
      ((rmwLoopMid op bits).map fun i => .ins i) ++
      [.ins (.stlxr bits (.x 24) (rmwLoopStored op) (.x 25)) fl.trapCode,
        .ins (.cbz true true (.x 24) l)] := by
  simp [rmwLoopLines, rmwLoopBody]

theorem kinds_rmwLoopLines (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) :
    kinds (rmwLoopLines bits op fl l) = [.acqXR, .relXW] := by
  rw [rmwLoopLines_eq, kinds_append, kinds_append, kinds_rmwLoopMid]
  rfl

theorem memInsns_append (a b : List Line) : memInsns (a ++ b) = memInsns a ++ memInsns b :=
  List.filterMap_append

/-- **The `atomic_rmw` loop's memory instructions**: `ldaxr x27, [x25]` then `stlxr w24, …,
[x25]`, at the same size and address register, nothing else (so they are `po`-adjacent). -/
theorem memInsns_rmwLoopLines (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (l : Lbl) : memInsns (rmwLoopLines bits op fl l) =
      [.ldaxr bits (.x 27) (.x 25), .stlxr bits (.x 24) (rmwLoopStored op) (.x 25)] := by
  have hmid : memInsns ((rmwLoopMid op bits).map fun i => .ins i) = [] := by
    rw [memInsns, List.filterMap_map, List.filterMap_eq_nil_iff]
    intro i hi
    simp [Function.comp, insnKind_rmwLoopMid op bits i hi]
  rw [rmwLoopLines_eq, memInsns_append, memInsns_append, hmid]
  rfl

/-- **The `atomic_cas` loop's memory instructions**: `ldaxr x27, [x25]` then `stlxr w24, x28,
[x25]`, at the same size and address register, nothing else. -/
theorem memInsns_casLoopLines (bits : Nat) (fl : Clif.MemFlags) (a b : Lbl) :
    memInsns (casLoopLines bits fl a b) =
      [.ldaxr bits (.x 27) (.x 25), .stlxr bits (.x 24) (.x 28) (.x 25)] := by
  simp only [casLoopLines, casLoopHead, memInsns, List.cons_append, List.nil_append,
    List.filterMap_cons, List.filterMap_nil, insnKind_casLoopCmp]
  rfl

theorem kinds_casLoopLines (bits : Nat) (fl : Clif.MemFlags) (a b : Lbl) :
    kinds (casLoopLines bits fl a b) = [.acqXR, .relXW] := by
  simp only [casLoopLines, casLoopHead, kinds, List.cons_append, List.nil_append,
    List.filterMap_cons, List.filterMap_nil, lineKind, insnKind_casLoopCmp]
  rfl

theorem kinds_memFinalize' {c : FnCtx} {m : AMode} {n : Nat} {v : List Line × AMode}
    (h : memFinalize c m n = .ok v) : kinds v.1 = [] :=
  kinds_memFinalize (m' := v.2) h

/-- **The memory-event kinds of every allocated instruction's code.** -/
theorem lines_kinds (c : FnCtx) (m : MInst) (ps : PState) {ls : List Line} {ps' : PState}
    (h : m.lines c ps = .ok (ls, ps')) : kinds ls = akinds m := by
  have okE : ∀ {α : Type} {a b : α}, (Except.ok a : Except String α) = .ok b → a = b :=
    fun h => by cases h; rfl
  have errE : ∀ {α : Type} {s : String} {b : α}, (throw s : Except String α) = .ok b → False :=
    fun h => by cases h
  cases m <;> simp only [MInst.lines, bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' split at h)
  all_goals first
    | (exfalso; apply errE; assumption)
    | (cases h; done)
    | (obtain ⟨rfl, -⟩ := Prod.mk.inj (okE h)
       first
        | rfl
        | (simp only [kinds_append, kinds_memFinalize (by assumption)]; rfl)
        | (simp only [kinds_append, kinds_memFinalize' (by assumption), kinds_addOff]; rfl)
        | (simp only [kinds_rmwLoopLines, kinds_casLoopLines]; rfl)
        | (simp only [kinds, List.filterMap_cons, List.filterMap_nil, List.filterMap_append,
            List.filterMap_map, lineKind, insnKind_condBr]
           simp [insnKind, akinds, Function.comp, lineKind]))

theorem kinds_const {k : AKind} : ∀ {ls : List Line}, (∀ l ∈ ls, lineKind l = some k) →
    kinds ls = List.replicate ls.length k
  | [], _ => rfl
  | l :: ls, h => by
    simp only [kinds, List.filterMap_cons, h l List.mem_cons_self, List.length_cons,
      List.replicate_succ]
    exact congrArg _ (kinds_const fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem kinds_spAdjLines (sub : Bool) (n : Nat) : kinds (spAdjLines sub n) = [] := by
  unfold spAdjLines
  split
  · rfl
  · split
    · cases sub <;> rfl
    · simp only [kinds_append, kinds_loadConst64]; cases sub <;> rfl

/-- Each push is one plain write. -/
theorem kinds_pushLines (int : Bool) (rs : List Reg) :
    kinds (pushLines int rs) = List.replicate (pushLines int rs).length .plainW := by
  apply kinds_const
  intro l hl
  simp only [pushLines, List.mem_append, List.mem_map] at hl
  rcases hl with hl | ⟨⟨a, b⟩, -, rfl⟩
  · split at hl
    · simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl
    · simp at hl
  · cases int <;> rfl

/-- Each pop is one plain read. -/
theorem kinds_popLines (int : Bool) (rs : List Reg) :
    kinds (popLines int rs) = List.replicate (popLines int rs).length .plainR := by
  apply kinds_const
  intro l hl
  simp only [popLines, List.mem_append, List.mem_map] at hl
  rcases hl with ⟨⟨a, b⟩, -, rfl⟩ | hl
  · cases int <;> rfl
  · split at hl
    · simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl
    · simp at hl

/-- `k` unrolled stack probes (#581): one plain write (`stur wzr`) each; `sub sp` accesses
nothing. -/
theorem kinds_probeSteps : ∀ k, kinds (probeSteps k) = List.replicate k .plainW
  | 0 => rfl
  | k + 1 => by rw [probeSteps, kinds_append, kinds_probeSteps k]; rfl

/-- The stack probes' store lines (#581): one per unrolled probe, the loop's single `str`. -/
def probeStores (total : Nat) : Nat := if 3 < probeCount total then 1 else probeCount total

/-- The stack probes (#581): one plain write per unrolled probe (the final `add sp` accesses
nothing), or the loop's `str wzr, [sp, x16]` (its constants, `sub`, `cmn` and `b.gt` access
nothing). (#581: the former count, `probeCount`, became false for the loop form, whose single
`str` runs once per iteration.) -/
theorem kinds_probeLines (total : Nat) :
    kinds (probeLines total) = List.replicate (probeStores total) .plainW := by
  unfold probeLines
  simp only
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    rw [probeStores, if_neg (by omega), h]; rfl
  · split
    · rename_i h3
      rw [kinds_append, kinds_probeSteps, probeStores, if_neg (by omega)]
      exact List.append_nil _
    · rename_i h3
      rw [probeStores, if_pos (by omega)]
      simp only [probeLoopLines, probeLoopBody, kinds_append, kinds_loadConst64, List.nil_append]
      rfl

/-- The frame setup stores fp/lr (`stp`), runs the stack probes (`stur wzr`, or the loop's `str`),
then pushes the saved registers: plain writes only. (#581: the former statement, without the
probes' writes, became false with Cranelift's stack probes; `calls` is the new argument of
`prologueLines`; the probes' count is `probeStores`.) -/
theorem kinds_prologueLines (saves : List Reg) (n : Nat) (calls : Bool) :
    kinds (prologueLines saves n calls) = .plainW :: List.replicate
      (probeStores (probeTotal n calls) +
        ((pushLines true (savesInt saves)).length + (pushLines false (savesFloat saves)).length))
      .plainW := by
  rw [← List.replicate_append_replicate, ← List.replicate_append_replicate]
  simp only [prologueLines, kinds_append, kinds_spAdjLines, kinds_pushLines, kinds_probeLines,
    List.append_nil, List.append_assoc]
  rfl

/-- The frame teardown pops the saved registers, then loads fp/lr (`ldp`): plain reads only. -/
theorem kinds_epilogueLines (saves : List Reg) (n : Nat) :
    kinds (epilogueLines saves n) = List.replicate
      ((popLines false (savesFloat saves)).length + (popLines true (savesInt saves)).length + 1)
      .plainR := by
  rw [List.replicate_succ', ← List.replicate_append_replicate]
  simp only [epilogueLines, kinds_append, kinds_spAdjLines, kinds_popLines, List.nil_append]
  rfl

theorem relaxable_some {ln : Line} {c : Insn} {t : Lbl} (h : ln.relaxable? = some (c, t)) :
    ln = .ins c none ∧ insnKind c = none ∧ ∀ l, insnKind (c.invertTo l) = none := by
  cases ln with
  | ins i tr =>
    cases tr with
    | some _ => simp [Line.relaxable?] at h
    | none =>
      simp only [Line.relaxable?, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', ht, rfl, -⟩ := h
      refine ⟨rfl, ?_, ?_⟩ <;>
        cases i <;> simp [Insn.relaxTarget?, Insn.condTarget?] at ht <;>
        first | rfl | (intro l; rfl)
  | word _ _ => simp [Line.relaxable?] at h
  | label _ => simp [Line.relaxable?] at h

/-- Branch relaxation rewrites only branches: the memory-event kinds are unchanged. -/
theorem kinds_relaxLines (far : Lbl → Bool) (ls : List Line) :
    kinds (relaxLines far ls) = kinds ls := by
  induction ls with
  | nil => rfl
  | cons ln ls ih =>
    rw [relaxLines, List.flatMap_cons, ← relaxLines, kinds_append, ih]
    show _ = kinds ([ln] ++ ls)
    rw [kinds_append]
    congr 1
    unfold relaxLine
    split
    · rename_i c t h
      obtain ⟨rfl, hc, hinv⟩ := relaxable_some h
      split
      · simp only [kinds, List.filterMap_cons, List.filterMap_nil, lineKind, hc, hinv]; rfl
      · rfl
    · rfl

/-- The allocated instructions implementing CLIF atomics and `fence`. -/
def atomicOrFence : MInst → Bool
  | .loadAcquire .. | .storeRelease .. | .atomicRmwLoop .. | .atomicCasLoop .. | .fence => true
  | _ => false

/-- **Acquire, release, exclusive and barrier events come only from CLIF atomics and `fence`.** -/
theorem ordered_only_atomic {c : FnCtx} {m : MInst} {ps : PState} {ls : List Line} {ps' : PState}
    (h : m.lines c ps = .ok (ls, ps')) {k : AKind} (hk : k ∈ kinds ls) (hr : k ≠ .plainR)
    (hw : k ≠ .plainW) : atomicOrFence m = true := by
  rw [lines_kinds c m ps h] at hk
  cases m <;> simp [akinds] at hk <;> simp_all [atomicOrFence]

/-- Non-vacuity of `lines_kinds` (its premise `m.lines c ps = .ok …` holds) at an `atomic_rmw`
loop, an `atomic_cas` loop, `ldar`, `stlr`
and `dmb ish`. -/
theorem lines_kinds_witness :
    let c : FnCtx := { k := 0, slotBase := 0 }
    let fl : Clif.MemFlags := {}
    (∃ ls ps', (MInst.atomicRmwLoop (.int 32) .add fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)).lines
        c {} = .ok (ls, ps') ∧ kinds ls = [.acqXR, .relXW]) ∧
    (∃ ls ps', (MInst.atomicCasLoop (.int 64) fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)).lines
        c {} = .ok (ls, ps') ∧ kinds ls = [.acqXR, .relXW]) ∧
    (∃ ls ps', (MInst.loadAcquire (.int 8) (.x 1) (.x 0) fl).lines c {} = .ok (ls, ps') ∧
        kinds ls = [.acqR]) ∧
    (∃ ls ps', (MInst.storeRelease (.int 16) (.x 1) (.x 0) fl).lines c {} = .ok (ls, ps') ∧
        kinds ls = [.relW]) ∧
    (∃ ls ps', MInst.fence.lines c {} = .ok (ls, ps') ∧ kinds ls = [.dmb]) := by
  intro c fl
  exact ⟨⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩, ⟨_, _, rfl, rfl⟩⟩

end Concurrency.Code
