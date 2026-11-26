import FVTest.Opt.MidValWitness
import FVTest.Opt.MidValNegWitness
import FV.Link.MidProgSyms

/-! # Witness: the hoisting mode at the executable's symbol table (#1119, `symbol_value` hoisting)

**Witness file** (`native_decide` allowed; not a compiler theorem). Two pairs of the measured
release crates (`FVTest/Opt/midval/real_symhoist*.{unopt,opt}.clif`, the dumps as cg_clif wrote
them; the shared corpus `~/clifv/shared/midval-corpus`), in which Cranelift's loop-invariant code
motion hoisted a `symbol_value` out of a loop, and the hand-made `neg_symhoist`
(`FVTest/Opt/MidValNegWitness.lean`):

* `real` (crypto-bigint's test build, proptest `_RNxC8proptest12HcH766IvbJwx`): main's
  per-function decision `Link.midPairB` rejects it; the hoisting mode accepts it
  (`Link.hoistCopy`), and **at the table of the names `g` itself references** (`ownSyms g`: every
  executable linking `g` defines them) `Link.midPairSymsB` holds, so `g` simulates `f` there
  (`real_simAt`) and `Link.midProgAt` applies with every premise discharged (`real_midProgAt`);
* `fold` (sha3 0.12.0, `_RNxC4sha311HvJs53D2OHO`): as `real`, and the hoisting mode accepts it
  only through the fold prep (the relaxed check without it, `checkC0 … (hoist := true)`,
  rejects; the accepted copy is not `ConstPhi.run f`);
* negative: at a table without those names (`fun _ => none`) `Link.midPairSymsB` rejects both real
  pairs; `neg_symhoist` is no simulation at the empty memory's table (`sh_not_simAt`), so
  `checkCertSymsAt` rejects it there for every certificate and hint list (`sh_symsAt_rejected`),
  as `checkCertC` does at every table (`sh_rejected`); at a table defining its symbol the hoisting
  mode accepts it (`sh_simAt`).
-/

namespace FVTest.Link.MidSymsWitness
open Clif Opt Opt.MidVal E2E Opt.MidVal.NegWitness
set_option autoImplicit false

def realFText : String := include_str "../Opt/midval/real_symhoist.unopt.clif"
def realGText : String := include_str "../Opt/midval/real_symhoist.opt.clif"
def foldFText : String := include_str "../Opt/midval/real_symhoist_fold.unopt.clif"
def foldGText : String := include_str "../Opt/midval/real_symhoist_fold.opt.clif"

def realF : Function := (RealWitness.decode realFText).getD default
def realG : Function := (RealWitness.decode realGText).getD default
def foldF : Function := (RealWitness.decode foldFText).getD default
def foldG : Function := (RealWitness.decode foldGText).getD default

/-- The symbol table of the names `g` references (its symbol globals and externs), each at `0`. -/
def ownSyms (g : Function) (n : String) : Option Nat :=
  if g.globals.any (fun p => match p.2 with
      | .symbol s _ _ | .tlsSymbol s _ _ => s == n
      | _ => false) || g.externs.any (·.2.name == n) then some 0 else none

/-- The table with no symbol. -/
def noSyms : String → Option Nat := fun _ => none

/-- The table defining `neg_symhoist`'s one symbol `s`. -/
def sSyms : String → Option Nat := fun n => if n == "s" then some 0 else none

/-- The one-function programs of the `real` pair. -/
def P0 : Program := { funcs := [realF] }
def Q : Program := { funcs := [realG] }

/-- Zero arguments of `realF`'s parameter types. -/
def args0 : List Val := realF.sig.params.map fun p => ⟨p.ty, 0⟩

/-- `realF`'s entry block. -/
def blk : Block := realF.entry?.getD default

/-- The registers of the entry block's parameters bound to `args0`. -/
def regs0 : Regs := (Regs.empty.setMany (blk.params.map (·.1)) args0).getD Regs.empty

/-- An entry state of `realF` on `args0` whose memory has the symbol table `ownSyms realG`. -/
def cs0 : State :=
  ⟨⟨realF, regs0, realF.slots.map fun s => (s.1, 0), blk.body, blk.term⟩, [],
    { symbols := ownSyms realG }⟩

/-- What `native_decide` evaluates. -/
def facts : Bool :=
  (RealWitness.decode realFText).isSome && (RealWitness.decode realGText).isSome &&
  (RealWitness.decode foldFText).isSome && (RealWitness.decode foldGText).isSome &&
  -- `real`: rejected per function, accepted by the hoisting mode at `g`'s own names only
  !Link.midPairB realF realG && (Link.hoistCopy realF realG).isSome &&
  Link.midValidatedSymsB (ownSyms realG) P0.funcs Q.funcs &&
  !Link.midPairSymsB noSyms realF realG &&
  -- `fold`: the same, through the fold prep
  !Link.midPairB foldF foldG && Link.midPairSymsB (ownSyms foldG) foldF foldG &&
  !Link.midPairSymsB noSyms foldF foldG &&
  !(checkC0 (ConstPhi.run foldF) foldG (hoist := true)).isOk &&
  !decide (Link.hoistCopy foldF foldG = some (ConstPhi.run foldF)) &&
  -- `neg_symhoist` at a table with its symbol
  Link.midPairSymsB sSyms shF shG &&
  -- the entry state of `realF`
  decide (P0.func? realF.name = some realF) && decide (Q.func? realF.name = some realG) &&
  decide (args0.map (·.ty) = realF.sig.params.map (·.ty)) &&
  decide (realF.entry? = some blk) && decide (blk.params.map (·.2) = args0.map (·.ty)) &&
  (Regs.empty.setMany (blk.params.map (·.1)) args0).isSome &&
  decide ((realF.slots.map fun s => (s.1, 0)).map (·.1) = realF.slots.map (·.1))

theorem facts_true : facts = true := by native_decide

theorem facts_spec :
    Link.midPairB realF realG = false ∧ (Link.hoistCopy realF realG).isSome = true ∧
    Link.midValidatedSymsB (ownSyms realG) P0.funcs Q.funcs = true ∧
    Link.midPairSymsB noSyms realF realG = false ∧
    Link.midPairB foldF foldG = false ∧ Link.midPairSymsB (ownSyms foldG) foldF foldG = true ∧
    Link.midPairSymsB noSyms foldF foldG = false ∧
    (checkC0 (ConstPhi.run foldF) foldG (hoist := true)).isOk = false ∧
    Link.hoistCopy foldF foldG ≠ some (ConstPhi.run foldF) ∧
    Link.midPairSymsB sSyms shF shG = true ∧
    P0.func? realF.name = some realF ∧ Q.func? realF.name = some realG ∧
    ClifEntry realF args0 cs0 := by
  have h := facts_true
  simp only [facts, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨-, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hf, hg, hsig, hb, hpar, hset,
    hslots⟩ := h
  have hreg : Regs.empty.setMany (blk.params.map (·.1)) args0 = some regs0 := by
    unfold regs0
    revert hset
    cases Regs.empty.setMany (blk.params.map (·.1)) args0 <;> simp
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hf, hg,
    ⟨rfl, rfl, hsig, ⟨blk, hb, rfl, rfl, hpar, hreg⟩, hslots⟩⟩

/-! ## The real pairs -/

/-- **`real`: `g` simulates `f` at the table of `g`'s own names**, by the decision
`Link.midValidatedSymsB` (`Link.midValidatedSymsB_sound`), though `Link.midPairB` rejects it. -/
theorem real_simAt : Link.midPairB realF realG = false ∧
    Opt.FunsSimMUAt (ownSyms realG) P0.funcs Q.funcs :=
  ⟨facts_spec.1, Link.midValidatedSymsB_sound facts_spec.2.2.1⟩

/-- The empty base environment keeps the symbols (it has no externs). -/
theorem keep_empty : Opt.EnvKeepsSymbols Env.empty := by
  intro name f h
  cases h

/-- **`Link.midProgAt` applies to the `real` pair** with every premise discharged: a return
(trap) of `P0`'s run from `realF`'s entry at the table `ownSyms realG` is one of `Q`'s run from
`realG`'s entry. -/
theorem real_midProgAt (M : Nat) :
    ClifEntry realG args0 (midEntry realG cs0) ∧
      (midEntry realG cs0).frame.slots = cs0.frame.slots ∧ (midEntry realG cs0).mem = cs0.mem ∧
    (∀ vals cm, Clif.runLoop Env.empty P0 M cs0 = .returned vals cm →
      ∃ m, Clif.runLoop Env.empty Q m (midEntry realG cs0) = .returned vals cm) ∧
    (∀ c, Clif.runLoop Env.empty P0 M cs0 = .trapped c →
      ∃ m, Clif.runLoop Env.empty Q m (midEntry realG cs0) = .trapped c) :=
  Link.midProgAt real_simAt.2 keep_empty facts_spec.2.2.2.2.2.2.2.2.2.2.1
    facts_spec.2.2.2.2.2.2.2.2.2.2.2.1 facts_spec.2.2.2.2.2.2.2.2.2.2.2.2 rfl M

/-- **`fold`: through the fold prep in the hoisting mode**: `Link.midPairB` and the relaxed
hoisting check without the prep reject it, `Link.midPairSymsB` at `g`'s own names accepts it
against a copy other than `ConstPhi.run f`, and `g` simulates `f` there. -/
theorem fold_simAt : Link.midPairB foldF foldG = false ∧
    (checkC0 (ConstPhi.run foldF) foldG (hoist := true)).isOk = false ∧
    Link.hoistCopy foldF foldG ≠ some (ConstPhi.run foldF) ∧
    Opt.FunSimMUAt (ownSyms foldG) foldF foldG :=
  ⟨facts_spec.2.2.2.2.1, facts_spec.2.2.2.2.2.2.2.1, facts_spec.2.2.2.2.2.2.2.2.1,
    Link.midPairSymsB_sound facts_spec.2.2.2.2.2.1⟩

/-- **Negative: without the symbols, the pairs are not covered**: at the table with no symbol
`Link.midPairSymsB` rejects both real pairs (decided). -/
theorem real_noSyms_rejected :
    Link.midPairSymsB noSyms realF realG = false ∧ Link.midPairSymsB noSyms foldF foldG = false :=
  ⟨facts_spec.2.2.2.1, facts_spec.2.2.2.2.2.2.1⟩

/-! ## `neg_symhoist` -/

/-- `FunSimMU.entry_rel` at one symbol table. -/
theorem FunSimMUAt.entry_rel {syms : String → Option Nat} {f g : Function}
    (hs : FunSimMUAt syms f g) {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    (hm : m.symbols = syms) :
    ∃ R, IsSimMU syms R ∧ R ⟨f, regs, [], b.body, b.term⟩ ⟨g, regs, [], b'.body, b'.term⟩ m := by
  obtain ⟨R, hR, he⟩ := hs.sim
  obtain ⟨b2, hb2, -, hrel⟩ := he b hb
  rw [hb'] at hb2
  cases hb2
  exact ⟨R, hR, hrel args regs [] m hty hr (by simp [hsl]) hm⟩

/-- `Opt.not_funSimMU_ret` at one symbol table: `f` steps once and returns, `g` is `stuck` at
once, from a memory with the symbols `syms`. -/
theorem not_funSimMUAt_ret {syms : String → Option Nat} {f g : Function} {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') {args : List Val} {regs : Regs} {m : Mem}
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs) (hsl : f.slots = [])
    (hm : m.symbols = syms)
    {fr1 : Frame} {vals : List Val} (hf1 : lstep ⟨f, regs, [], b.body, b.term⟩ m = .next fr1 m)
    (hf2 : lstep fr1 m = .ret vals)
    (hg : ∃ msg, lstep ⟨g, regs, [], b'.body, b'.term⟩ m = .stuck msg) :
    ¬ FunSimMUAt syms f g := by
  intro hs
  obtain ⟨R, hR, hrel⟩ := FunSimMUAt.entry_rel hs hb hb' hty hr hsl hm
  obtain ⟨msg, hgs⟩ := hg
  have hgn : ∀ fr1 m1, lstep ⟨g, regs, [], b'.body, b'.term⟩ m ≠ .next fr1 m1 := by
    intro _ _ h; rw [hgs] at h; cases h
  obtain ⟨g1, hs1, hr1⟩ := hR.toIsSimM.next hrel hm hf1
  obtain ⟨rfl, -⟩ := LStar.of_no_next hgn hs1
  obtain ⟨fr2, hs2, hret⟩ := hR.toIsSimM.ret hr1 hm hf2
  obtain ⟨rfl, -⟩ := LStar.of_no_next hgn hs2
  rw [hgs] at hret
  cases hret

/-- **`neg_symhoist` is no simulation at the empty memory's table** (`sh_not_sim`'s run: with
`v1 = 0`, `f` returns, `g` is `stuck` on the `symbol_value` of the missing symbol). -/
theorem sh_not_simAt : ¬ FunSimMUAt Mem.empty.symbols shF shG :=
  not_funSimMUAt_ret (b := shB) (b' := shB') (args := [⟨.i64, 0⟩, ⟨.i64, 0⟩]) (regs := hoRegs)
    (m := Mem.empty) (fr1 := ⟨shF, hoRegs, [], [], .ret [0]⟩) (vals := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl⟩

/-- **`neg_symhoist` is rejected at a table without its symbol**: `checkCertSymsAt` rejects every
certificate and hint list there. -/
theorem sh_symsAt_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertSymsAt Mem.empty.symbols (ConstPhi.run shF) shG cert hints = false := by
  cases h : checkCertSymsAt Mem.empty.symbols (ConstPhi.run shF) shG cert hints
  · rfl
  · exact absurd (checkedSymsAt_simMUAt h) sh_not_simAt

/-- **`neg_symhoist` at a table defining its symbol**: the hoisting mode accepts it there
(`Link.midPairSymsB`, decided), so `g` simulates `f` at that table, while `checkCertC` rejects it
with every certificate and hint list (`sh_rejected`, every table). -/
theorem sh_simAt : FunSimMUAt sSyms shF shG ∧
    ∀ cert hints, checkCertC (ConstPhi.run shF) shG cert hints = false :=
  ⟨Link.midPairSymsB_sound facts_spec.2.2.2.2.2.2.2.2.2.1, sh_rejected⟩

end FVTest.Link.MidSymsWitness
