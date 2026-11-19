import FVTest.Opt.MidValPairs
import FV.Opt.Proof.MidValNeg
import FV.Opt.Proof.MidValProg

/-! # Negative witnesses of the mid-end validator (#1119)

Three of the hand-made negative pairs of `FVTest/Opt/MidValPairs.lean`, as `Clif.Function` terms
(equal to the parsed texts, `*_text`, decided): for each, `g` does NOT simulate `f`
(`¬ FunSimMU f g`, from one run each, `not_funSimMU_trap` / `not_funSimMU_ret`), so by
`check_sound` the re-check rejects **every** certificate (`*_rejected`):

* `neg_deadload`: a dead load with a trap code removed: `f` traps (`heap_oob` on an empty
  memory), `g` returns;
* `neg_stuckpure`: an ill-typed `fadd` evaluated by `g` where `f` does not: `g` is `stuck`, `f`
  returns (the reason pure nodes must be total on their checked types);
* `neg_hoist`: a `can_move` load hoisted above its guard: `g` is `stuck` on the bad address, `f`
  takes the other branch and returns. -/

namespace Opt.MidVal.NegWitness

open Clif

def ap (t : Ty) : AbiParam := { ty := t, ext := .none, purpose := .normal }

def sig1 : Signature := { params := [ap .i64], returns := [ap .i64], callConv := none }
def sig2 : Signature := { params := [ap .f64, ap .i8], returns := [ap .f64], callConv := none }
def sig3 : Signature := { params := [ap .i64, ap .i64], returns := [ap .i64], callConv := none }

def trapFl : MemFlags :=
  { trapCode := some .heapOob, aligned := false, readonly := false, canMove := false, endianness := none }
def moveFl : MemFlags :=
  { trapCode := none, aligned := false, readonly := true, canMove := true, endianness := none }

/-! ## `neg_deadload` -/

def deadB : Block :=
  { id := 0, params := [(0, .i64)], cold := false,
    body := [{ results := [1], inst := .load .load .i64 trapFl 0 0 }], term := .ret [0] }
def deadB' : Block := { id := 0, params := [(0, .i64)], cold := false, body := [], term := .ret [0] }
def deadF : Function := { name := "f", sig := sig1, blocks := [deadB] }
def deadG : Function := { name := "f", sig := sig1, blocks := [deadB'] }

theorem deadF_text : Pairs.fn? "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = load.i64 v0\n    return v0\n}" = some deadF := by native_decide
theorem deadG_text : Pairs.fn? "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}" = some deadG := by native_decide

theorem dead_not_sim : ¬ FunSimMU deadF deadG := by
  refine not_funSimMU_trap (b := deadB) (b' := deadB') (args := [⟨.i64, 0⟩])
    (regs := Regs.empty.set 0 ⟨.i64, 0⟩) (m := Mem.empty) (c := .heapOob) rfl rfl rfl rfl rfl
    rfl ?_ ?_
  · intro fr1 m1 h; cases h
  · intro c h; cases h

/-- The re-check rejects every certificate for `neg_deadload`. -/
theorem dead_rejected (cert : Cert) : checkCert (ConstPhi.run deadF) deadG cert = false := by
  cases h : checkCert (ConstPhi.run deadF) deadG cert
  · rfl
  · exact absurd (checked_simMU h) dead_not_sim

/-! ## `neg_stuckpure` -/

def br : Terminator := .brif 1 { block := 1, args := [] } { block := 2, args := [] }
def stB1 : Block := { id := 1, params := [], cold := false, body := [], term := .ret [0] }
def stB2 : Block := { id := 2, params := [], cold := false, body := [], term := .ret [0] }
def stB : Block := { id := 0, params := [(0, .f64), (1, .i8)], cold := false, body := [], term := br }
def stB' : Block :=
  { id := 0, params := [(0, .f64), (1, .i8)], cold := false,
    body := [{ results := [9], inst := .float .fadd .f64 [0, 1] }], term := br }
def stF : Function := { name := "f", sig := sig2, blocks := [stB, stB1, stB2] }
def stG : Function := { name := "f", sig := sig2, blocks := [stB', stB1, stB2] }

theorem stF_text : Pairs.fn? "function %f(f64, i8) -> f64 {\nblock0(v0: f64, v1: i8):\n    brif v1, block1, block2\nblock1:\n    return v0\nblock2:\n    return v0\n}" = some stF := by native_decide
theorem stG_text : Pairs.fn? "function %f(f64, i8) -> f64 {\nblock0(v0: f64, v1: i8):\n    v9 = fadd.f64 v0, v1\n    brif v1, block1, block2\nblock1:\n    return v0\nblock2:\n    return v0\n}" = some stG := by native_decide

def stRegs : Regs := (Regs.empty.set 0 ⟨.f64, 0⟩).set 1 ⟨.i8, 0⟩

theorem st_not_sim : ¬ FunSimMU stF stG :=
  not_funSimMU_ret (b := stB) (b' := stB') (args := [⟨.f64, 0⟩, ⟨.i8, 0⟩]) (regs := stRegs)
    (m := Mem.empty) (fr1 := ⟨stF, stRegs, [], [], .ret [0]⟩) (vals := [⟨.f64, 0⟩])
    rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl⟩

/-- The re-check rejects every certificate for `neg_stuckpure`. -/
theorem st_rejected (cert : Cert) : checkCert (ConstPhi.run stF) stG cert = false := by
  cases h : checkCert (ConstPhi.run stF) stG cert
  · rfl
  · exact absurd (checked_simMU h) st_not_sim

/-! ## `neg_hoist` -/

def hoLd : Stmt := { results := [2], inst := .load .load .i64 moveFl 0 0 }
def hoB : Block := { id := 0, params := [(0, .i64), (1, .i64)], cold := false, body := [], term := br }
def hoB' : Block := { id := 0, params := [(0, .i64), (1, .i64)], cold := false, body := [hoLd], term := br }
def hoB1 : Block := { id := 1, params := [], cold := false, body := [hoLd], term := .ret [2] }
def hoB1' : Block := { id := 1, params := [], cold := false, body := [], term := .ret [2] }
def hoF : Function := { name := "f", sig := sig3, blocks := [hoB, hoB1, stB2] }
def hoG : Function := { name := "f", sig := sig3, blocks := [hoB', hoB1', stB2] }

theorem hoF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    brif v1, block1, block2\nblock1:\n    v2 = load.i64 notrap readonly can_move v0\n    return v2\nblock2:\n    return v0\n}" = some hoF := by native_decide
theorem hoG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly can_move v0\n    brif v1, block1, block2\nblock1:\n    return v2\nblock2:\n    return v0\n}" = some hoG := by native_decide

def hoRegs : Regs := (Regs.empty.set 0 ⟨.i64, 0⟩).set 1 ⟨.i64, 0⟩

theorem ho_not_sim : ¬ FunSimMU hoF hoG :=
  not_funSimMU_ret (b := hoB) (b' := hoB') (args := [⟨.i64, 0⟩, ⟨.i64, 0⟩]) (regs := hoRegs)
    (m := Mem.empty) (fr1 := ⟨hoF, hoRegs, [], [], .ret [0]⟩) (vals := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl⟩

/-- The re-check rejects every certificate for `neg_hoist`. -/
theorem ho_rejected (cert : Cert) : checkCert (ConstPhi.run hoF) hoG cert = false := by
  cases h : checkCert (ConstPhi.run hoF) hoG cert
  · rfl
  · exact absurd (checked_simMU h) ho_not_sim

end Opt.MidVal.NegWitness
