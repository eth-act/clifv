module

public import FV.Concurrency.Armv8

@[expose] public section

/-!
# Litmus tests of the Armv8 fragment against herd7's verdicts (T2c, #301)

The classic litmus tests, written with the instructions Cranelift emits for the CLIF programs they
come from (`str`/`ldr` for `store`/`load`, `stlr`/`ldar` for `atomic_store`/`atomic_load`,
`ldaxr`/`stlxr` loops for `atomic_rmw`/`atomic_cas`, `dmb ish` for `fence`). For each test and
outcome the candidate execution is unique: reads-from follows from the (distinct) values, and
coherence from initial writes first and the final values. The oracle is the verdict of herd7 with
the Armv8 model `aarch64.cat` (Arm ARM B2.3; Pulte et al., POPL 2018); qemu is not weak-memory
faithful and only checks the other direction (`scripts/litmus-qemu.sh`: observed ⊆ allowed).

* forbidden by herd7 ⇒ `¬ Armv8.Consistent` (an `ob` cycle, an internal cycle, or the atomic axiom);
* allowed by herd7 ⇒ `Armv8.Consistent` (rank certificates, kernel-decided).

| Test | Code | Outcome | herd7 | here |
| --- | --- | --- | --- | --- |
| MP+rel+acq | `str x; stlr y ‖ ldar y; ldr x` | y=1, x=0 | forbidden | `mp_rel_acq` |
| MP | `str x; str y ‖ ldr y; ldr x` | y=1, x=0 | allowed | `mp_plain` |
| MP+rel | `str x; stlr y ‖ ldr y; ldr x` | y=1, x=0 | allowed | `mp_rel` |
| MP+dmbs | `str x; dmb; str y ‖ ldr y; dmb; ldr x` | y=1, x=0 | forbidden | `mp_dmbs` |
| SB+rel+acq | `stlr x; ldar y ‖ stlr y; ldar x` | 0, 0 | forbidden | `sb_rel_acq` |
| SB | `str x; ldr y ‖ str y; ldr x` | 0, 0 | allowed | `sb_plain` |
| SB+dmbs | `str x; dmb; ldr y ‖ str y; dmb; ldr x` | 0, 0 | forbidden | `sb_dmbs` |
| LB+acq+rel | `ldar x; stlr y ‖ ldar y; stlr x` | 1, 1 | forbidden | `lb_acq_rel` |
| LB | `ldr x; str y ‖ ldr y; str x` | 1, 1 | allowed | `lb_plain` |
| 2+2W+rels | `stlr x=1; stlr y=2 ‖ stlr y=1; stlr x=2` | x=1, y=1 | forbidden | `w22_rels` |
| 2+2W | the same with `str` | x=1, y=1 | allowed | `w22_plain` |
| IRIW+acqs | `stlr x ‖ stlr y ‖ ldar x; ldar y ‖ ldar y; ldar x` | 1,0,1,0 | forbidden | `iriw_acqs`|
| IRIW | the same with `str`/`ldr` | 1,0,1,0 | allowed | `iriw_plain` |
| CoRR | `str x=1 ‖ ldr x; ldr x` | 1, 0 | forbidden | `corr` |
| ATOM-INC | two `atomic_rmw add` loops | both read 0 | forbidden | `inc_both0_a`, `inc_both0_b` |
| ATOM-INC | two `atomic_rmw add` loops | 0, 1 | allowed | `inc_ok` |

The model omits `dob` (dependencies), so tests whose verdict needs a dependency (e.g.
`MP+dmb+addr`, forbidden by herd7) are allowed here: the model is weaker than Armv8 by
construction (`docs/plans/atomics.md` §2; `FVTest/Concurrency/LitmusFull.lean`: `MP+dmb+addr` against
the full model); Cranelift's atomics never rely on dependencies.
-/

namespace Concurrency.Litmus

open Rel

-- the decided goals are disjunctions over a few events; instance synthesis needs more room
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- A litmus candidate execution on events `Fin n`, as lists indexed by event. -/
structure Lit (n : Nat) where
  tid : List Nat
  kind : List AKind
  loc : List Nat
  po : List (Nat × Nat)
  rf : List (Nat × Nat)
  co : List (Nat × Nat)
  rmw : List (Nat × Nat) := []
  /-- elements that hold no event (empty program positions, `Exec.ev`) -/
  noev : List Nat := []

abbrev Lit.exec {n : Nat} (t : Lit n) : Exec (Fin n) where
  tid e := t.tid.getD e.val 0
  dir e := (t.kind.getD e.val .dmb).dir
  loc e := t.loc.getD e.val 0
  po a b := (a.val, b.val) ∈ t.po
  rf a b := (a.val, b.val) ∈ t.rf
  co a b := (a.val, b.val) ∈ t.co
  rmw a b := (a.val, b.val) ∈ t.rmw
  ev e := e.val ∉ t.noev

abbrev Lit.ak {n : Nat} (t : Lit n) (e : Fin n) : AKind := t.kind.getD e.val .dmb

theorem Lit.kindOk {n : Nat} (t : Lit n) : Armv8.KindOk t.exec t.ak := fun _ => rfl

/-- A path `a → c₁ → … → b`. -/
def PathTo {α : Type} (r : Rel α) : α → List α → α → Prop
  | a, [], b => r a b
  | a, c :: cs, b => r a c ∧ PathTo r c cs b

theorem PathTo.plus {α : Type} {r : Rel α} : ∀ {a : α} {l : List α} {b : α},
    PathTo r a l b → Relation.TransGen r a b
  | _, [], _, h => .single h
  | _, _ :: _, _, ⟨h1, h2⟩ => (Relation.TransGen.single h1).trans (PathTo.plus h2)

/-- An `ob` cycle through the listed events. -/
syntax "ob_cycle" term:max term:max : tactic
macro_rules
  | `(tactic| ob_cycle $a $l) =>
    `(tactic| exact fun hc => hc.external $a (PathTo.plus (l := $l) (by
        simp only [PathTo, Armv8.ob, Armv8.obs, Armv8.bob, Armv8.A, Armv8.L, Exec.ext, Exec.fr]
        decide)))

/-- Consistency by one rank for the internal and external axioms. -/
syntax "consistent_by" term:max : tactic
macro_rules
  | `(tactic| consistent_by $f) =>
    `(tactic| exact {
        internal := acyclic_of_rank $f (by
          simp only [union, Exec.poLoc, Exec.com, Exec.fr]; decide)
        atomic := by simp only [Exec.ext, Exec.fr]; decide
        external := acyclic_of_rank $f (by
          simp only [Armv8.ob, Armv8.obs, Armv8.bob, Armv8.A, Armv8.L, Exec.ext, Exec.fr]
          decide) })

/-! ## MP (message passing). Events: 0 init x, 1 init y, thread 0: 2 data store, 3 flag store;
thread 1: 4 flag load (reads 3), 5 data load (reads the init 0). -/

def mpT (k3 k4 : AKind) : Lit 6 where
  tid := [10, 11, 0, 0, 1, 1]
  kind := [.plainW, .plainW, .plainW, k3, k4, .plainR]
  loc := [0, 1, 0, 1, 1, 0]
  po := [(2, 3), (4, 5)]
  rf := [(3, 4), (0, 5)]
  co := [(0, 2), (1, 3)]

/-- Rank of the MP candidates (init, data load, data store, flag store, flag load). -/
abbrev mpRank (e : Fin 6) : Nat := [0, 0, 2, 3, 4, 1].getD e.val 0

/-- **MP+rel+acq: forbidden** (`po;[L]`, `rfe`, `[A];po`, `fre`). -/
theorem mp_rel_acq : (mpT .relW .acqR).exec.Wf ∧
    ¬ Armv8.Consistent (mpT .relW .acqR).exec (mpT .relW .acqR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [3, 4, 5]

/-- **MP: allowed.** -/
theorem mp_plain : (mpT .plainW .plainR).exec.Wf ∧
    Armv8.Consistent (mpT .plainW .plainR).exec (mpT .plainW .plainR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by mpRank

/-- **MP+rel (release flag, plain flag load): allowed** (the reader is not ordered). -/
theorem mp_rel : (mpT .relW .plainR).exec.Wf ∧
    Armv8.Consistent (mpT .relW .plainR).exec (mpT .relW .plainR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by mpRank

/-- MP+dmbs. Events: 0 init x, 1 init y; thread 0: 2 `str x`, 3 `dmb`, 4 `str y`; thread 1:
5 `ldr y` (reads 4), 6 `dmb`, 7 `ldr x` (reads 0). -/
def mpDmbs : Lit 8 where
  tid := [10, 11, 0, 0, 0, 1, 1, 1]
  kind := [.plainW, .plainW, .plainW, .dmb, .plainW, .plainR, .dmb, .plainR]
  loc := [0, 1, 0, 9, 1, 1, 9, 0]
  po := [(2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)]
  rf := [(4, 5), (0, 7)]
  co := [(0, 2), (1, 4)]

/-- **MP+dmbs: forbidden.** -/
theorem mp_dmbs : mpDmbs.exec.Wf ∧ ¬ Armv8.Consistent mpDmbs.exec mpDmbs.ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [4, 5, 7]

/-! ## SB (store buffering). Events: 0 init x, 1 init y; thread 0: 2 store x, 3 load y (reads
1); thread 1: 4 store y, 5 load x (reads 0). -/

def sbT (kw : AKind) (kr : AKind) : Lit 6 where
  tid := [10, 11, 0, 0, 1, 1]
  kind := [.plainW, .plainW, kw, kr, kw, kr]
  loc := [0, 1, 0, 1, 1, 0]
  po := [(2, 3), (4, 5)]
  rf := [(1, 3), (0, 5)]
  co := [(0, 2), (1, 4)]

abbrev sbRank (e : Fin 6) : Nat := [0, 0, 2, 1, 2, 1].getD e.val 0

/-- **SB+rel+acq: forbidden** (`[L];po;[A]`: Armv8 is RCsc). -/
theorem sb_rel_acq : (sbT .relW .acqR).exec.Wf ∧
    ¬ Armv8.Consistent (sbT .relW .acqR).exec (sbT .relW .acqR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [3, 4, 5]

/-- **SB: allowed.** -/
theorem sb_plain : (sbT .plainW .plainR).exec.Wf ∧
    Armv8.Consistent (sbT .plainW .plainR).exec (sbT .plainW .plainR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by sbRank

/-- SB+dmbs. Events: 0 init x, 1 init y; thread 0: 2 `str x`, 3 `dmb`, 4 `ldr y` (reads 1);
thread 1: 5 `str y`, 6 `dmb`, 7 `ldr x` (reads 0). -/
def sbDmbs : Lit 8 where
  tid := [10, 11, 0, 0, 0, 1, 1, 1]
  kind := [.plainW, .plainW, .plainW, .dmb, .plainR, .plainW, .dmb, .plainR]
  loc := [0, 1, 0, 9, 1, 1, 9, 0]
  po := [(2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)]
  rf := [(1, 4), (0, 7)]
  co := [(0, 2), (1, 5)]

/-- **SB+dmbs: forbidden.** -/
theorem sb_dmbs : sbDmbs.exec.Wf ∧ ¬ Armv8.Consistent sbDmbs.exec sbDmbs.ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [4, 5, 7]

/-! ## LB (load buffering). Events: 0 init x, 1 init y; thread 0: 2 load x (reads 5), 3 store y;
thread 1: 4 load y (reads 3), 5 store x. -/

def lbT (kr kw : AKind) : Lit 6 where
  tid := [10, 11, 0, 0, 1, 1]
  kind := [.plainW, .plainW, kr, kw, kr, kw]
  loc := [0, 1, 0, 1, 1, 0]
  po := [(2, 3), (4, 5)]
  rf := [(5, 2), (3, 4)]
  co := [(0, 5), (1, 3)]

abbrev lbRank (e : Fin 6) : Nat := [0, 0, 2, 1, 2, 1].getD e.val 0

/-- **LB+acq+rel: forbidden.** -/
theorem lb_acq_rel : (lbT .acqR .relW).exec.Wf ∧
    ¬ Armv8.Consistent (lbT .acqR .relW).exec (lbT .acqR .relW).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [3, 4, 5]

/-- **LB: allowed** (no dependencies). -/
theorem lb_plain : (lbT .plainR .plainW).exec.Wf ∧
    Armv8.Consistent (lbT .plainR .plainW).exec (lbT .plainR .plainW).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by lbRank

/-! ## 2+2W. Events: 0 init x, 1 init y; thread 0: 2 `x=1`, 3 `y=2`; thread 1: 4 `y=1`, 5 `x=2`;
final `x=1`, `y=1`: `co` is 0, 5, 2 on x and 1, 3, 4 on y. -/

def w22T (k : AKind) : Lit 6 where
  tid := [10, 11, 0, 0, 1, 1]
  kind := [.plainW, .plainW, k, k, k, k]
  loc := [0, 1, 0, 1, 1, 0]
  po := [(2, 3), (4, 5)]
  rf := []
  co := [(0, 5), (0, 2), (5, 2), (1, 3), (1, 4), (3, 4)]

abbrev w22Rank (e : Fin 6) : Nat := [0, 0, 2, 1, 2, 1].getD e.val 0

/-- **2+2W+rels: forbidden.** -/
theorem w22_rels : (w22T .relW).exec.Wf ∧ ¬ Armv8.Consistent (w22T .relW).exec (w22T .relW).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [3, 4, 5]

/-- **2+2W: allowed.** -/
theorem w22_plain : (w22T .plainW).exec.Wf ∧
    Armv8.Consistent (w22T .plainW).exec (w22T .plainW).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by w22Rank

/-! ## IRIW. Events: 0 init x, 1 init y; 2 `x=1` (thread 0), 3 `y=1` (thread 1); thread 2:
4 load x (reads 2), 5 load y (reads 1); thread 3: 6 load y (reads 3), 7 load x (reads 0). -/

def iriwT (kw kr : AKind) : Lit 8 where
  tid := [10, 11, 0, 1, 2, 2, 3, 3]
  kind := [.plainW, .plainW, kw, kw, kr, kr, kr, kr]
  loc := [0, 1, 0, 1, 0, 1, 1, 0]
  po := [(4, 5), (6, 7)]
  rf := [(2, 4), (1, 5), (3, 6), (0, 7)]
  co := [(0, 2), (1, 3)]

abbrev iriwRank (e : Fin 8) : Nat := [0, 0, 2, 2, 3, 1, 3, 1].getD e.val 0

/-- **IRIW+acqs: forbidden** (Armv8 is multi-copy atomic). -/
theorem iriw_acqs : (iriwT .relW .acqR).exec.Wf ∧
    ¬ Armv8.Consistent (iriwT .relW .acqR).exec (iriwT .relW .acqR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  ob_cycle 2 [4, 5, 3, 6, 7]

/-- **IRIW: allowed.** -/
theorem iriw_plain : (iriwT .plainW .plainR).exec.Wf ∧
    Armv8.Consistent (iriwT .plainW .plainR).exec (iriwT .plainW .plainR).ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by iriwRank

/-! ## CoRR. Events: 0 init x, 1 `x=1` (thread 0); thread 1: 2 load x (reads 1), 3 load x
(reads 0). -/

def corrT : Lit 4 where
  tid := [10, 0, 1, 1]
  kind := [.plainW, .plainW, .plainR, .plainR]
  loc := [0, 0, 0, 0]
  po := [(2, 3)]
  rf := [(1, 2), (0, 3)]
  co := [(0, 1)]

theorem corr_wf : corrT.exec.Wf := by constructor <;> decide

/-- **CoRR: forbidden** (SC per location: `po-loc`, `fr`, `rf`). -/
theorem corr : ¬ Armv8.Consistent corrT.exec corrT.ak := fun hc =>
  hc.internal 2 (PathTo.plus (l := [3, 1]) (by
    simp only [PathTo, union, Exec.poLoc, Exec.com, Exec.fr]; decide))

/-! ## ATOM-INC: two `atomic_rmw add` LL/SC loops on x. Events: 0 init x; thread 0: 1 `ldaxr`,
2 `stlxr`; thread 1: 3 `ldaxr`, 4 `stlxr`. -/

/-- Both loads read the initial value; `co` orders thread 0's write first (`a`) or last
(`b`). -/
def incT (first0 : Bool) : Lit 5 where
  tid := [10, 0, 0, 1, 1]
  kind := [.plainW, .acqXR, .relXW, .acqXR, .relXW]
  loc := [0, 0, 0, 0, 0]
  po := [(1, 2), (3, 4)]
  rf := [(0, 1), (0, 3)]
  co := if first0 then [(0, 2), (0, 4), (2, 4)] else [(0, 2), (0, 4), (4, 2)]
  rmw := [(1, 2), (3, 4)]

theorem inc_wf (b : Bool) : (incT b).exec.Wf := by
  cases b <;> constructor <;> decide

/-- **ATOM-INC, both read 0, thread 0's write first: forbidden** (the atomic axiom on thread 1's
pair). -/
theorem inc_both0_a : ¬ Armv8.Consistent (incT true).exec (incT true).ak := fun hc =>
  hc.atomic 3 4 (by decide) ⟨2, by simp only [Exec.ext, Exec.fr]; decide⟩

/-- **ATOM-INC, both read 0, thread 1's write first: forbidden.** -/
theorem inc_both0_b : ¬ Armv8.Consistent (incT false).exec (incT false).ak := fun hc =>
  hc.atomic 1 2 (by decide) ⟨4, by simp only [Exec.ext, Exec.fr]; decide⟩

/-- Thread 0 reads 0, thread 1 reads thread 0's 1. -/
def incOk : Lit 5 where
  tid := [10, 0, 0, 1, 1]
  kind := [.plainW, .acqXR, .relXW, .acqXR, .relXW]
  loc := [0, 0, 0, 0, 0]
  po := [(1, 2), (3, 4)]
  rf := [(0, 1), (2, 3)]
  co := [(0, 2), (0, 4), (2, 4)]
  rmw := [(1, 2), (3, 4)]

/-- **ATOM-INC 0, 1: allowed.** -/
theorem inc_ok : incOk.exec.Wf ∧ Armv8.Consistent incOk.exec incOk.ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by (fun e : Fin 5 => e.val)

/-! ## Empty positions inside an exclusive pair (`Exec.Wf.rmw_imm`). Events: 0 init x; thread 0:
1 `ldaxr`, 2 a position after it in its step, 3 `stlxr`. -/

/-- Position 2 holds no event (`ev2 = false`, the `ldaxr` step's empty second slot) or holds a
`dmb` (`ev2 = true`). -/
def gapT (ev2 : Bool) : Lit 4 where
  tid := [10, 0, 0, 0]
  kind := [.plainW, .acqXR, .dmb, .relXW]
  loc := [0, 0, 0, 0]
  po := [(1, 2), (2, 3), (1, 3)]
  rf := [(0, 1)]
  co := [(0, 3)]
  rmw := [(1, 3)]
  noev := if ev2 then [] else [2]

/-- **An empty position between the pair keeps the execution well formed** (it is not strictly
well formed: the first model's immediacy quantified over every position). -/
theorem gap_empty_wf : (gapT false).exec.Wf ∧ ¬ (gapT false).exec.WfStrict :=
  ⟨by constructor <;> decide, fun h => h.rmw_imm_all 1 3 2 (by decide) (by decide) (by decide)⟩

/-- **A fence between the pair is not well formed.** -/
theorem gap_fence_not_wf : ¬ (gapT true).exec.Wf := fun h =>
  h.rmw_imm 1 3 2 (by decide) (by decide) (by decide) (.inr (by decide))

end Concurrency.Litmus
