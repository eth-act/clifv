import FVTest.Opt.MidValPairs
import FV.Opt.Proof.MidValNeg
import FV.Opt.Proof.MidValProg
import FV.Opt.Proof.MidValCondProg

/-! # Negative witnesses of the mid-end validator (#1119)

The hand-made negative pairs of `FVTest/Opt/MidValPairs.lean` (`FVTest/Opt/midval/neg_*`), as
`Clif.Function` terms (equal to the parsed texts, `*_text`, by `native_decide`). For seven of
the eight, `g` does NOT simulate `f` (`¬ FunSimMU f g`, from one concrete run of each side,
criteria of `FV/Opt/Proof/MidValNeg.lean`; the runs are checked by `rfl`), so by `check_sound`
the re-check rejects **every** certificate (`*_rejected`):

* `neg_deadload`: a dead load with a trap code removed: `f` traps (`heap_oob` on an empty
  memory), `g` returns;
* `neg_stuckpure`: an ill-typed `fadd` evaluated by `g` where `f` does not: `g` is `stuck`, `f`
  returns (the reason pure nodes must be total on their checked types);
* `neg_hoist`: a `can_move` load hoisted above its guard: `g` is `stuck` on the bad address, `f`
  takes the other branch and returns;
* `neg_endian`: a big-endian load forwarded from a little-endian store: with `v0 = 0` in an
  8-byte allocation and `v1 = 1`, `f` returns `0x0100000000000000`, `g` returns `1`
  (`not_funSimMU_ret_ne`);
* `neg_merge`: forwarding across a join one of whose paths stores: with `v1 = 1`, `v2 = 2`, `f`
  takes the storing path and returns `2`, `g` returns `1` (`not_funSimMU_ret_ne`);
* `neg_readonly`: two `readonly` loads merged across a store (the flag is a hint: the semantics
  loads what is there): from a zeroed allocation with `v1 = 1`, `f` returns `0 + 1`, `g` returns
  `0 + 0` (`not_funSimMU_ret_ne`);
* `neg_call`: a store forwarded across a call: the callee may leave any memory with the same
  symbols; when it leaves zeros, `f` reloads and returns `0`, `g` returns `1`
  (`not_funSimMU_call_ret`).

Also (#1119 `placement:symbol_value`, not a file of `FVTest/Opt/midval`): `neg_symhoist`, a
`symbol_value` evaluated by `g` before the branch where `f` evaluates it on one side only (the
shape of Cranelift's loop-invariant hoisting): with no symbols, `g` is `stuck`, `f` returns
(`sh_not_sim`), so `checkCertC` rejects every certificate and hint list (`sh_rejected`).

`neg_type` is different: it IS a simulation, and the checker is merely conservative. Memory is
little-endian, so after `store.i64 v1, v0` the `load.i32 v0` reads exactly the low 32 bits of
`v1` (= `ireduce.i32 v1`): the load is in bounds whenever the store was (a prefix of the same
access, no alignment flag), its bytes are the ones just written, and an out-of-bounds or
read-only store traps or is `stuck` at the same step in both functions. The witness for it is
that the executable check rejects the pair (`ty_check_rejects`). -/

namespace Opt.MidVal.NegWitness

open Clif

def ap (t : Ty) : AbiParam := { ty := t, ext := .none, purpose := .normal }

def sig1 : Signature := { params := [ap .i64], returns := [ap .i64], callConv := none }
def sig2 : Signature := { params := [ap .f64, ap .i8], returns := [ap .f64], callConv := none }
def sig3 : Signature := { params := [ap .i64, ap .i64], returns := [ap .i64], callConv := none }
def sig4 : Signature :=
  { params := [ap .i64, ap .i64, ap .i64], returns := [ap .i64], callConv := none }

def trapFl : MemFlags :=
  { trapCode := some .heapOob, aligned := false, readonly := false, canMove := false, endianness := none }
def moveFl : MemFlags :=
  { trapCode := none, aligned := false, readonly := true, canMove := true, endianness := none }
def bigFl : MemFlags :=
  { trapCode := some .heapOob, aligned := false, readonly := false, canMove := false,
    endianness := some .big }
def roFl : MemFlags :=
  { trapCode := none, aligned := false, readonly := true, canMove := false, endianness := none }

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

/-! ## `neg_symhoist` (#1119 `placement:symbol_value`)

Cranelift's LICM moves a `symbol_value` (pure, no operands) out of a loop into its preheader,
so `g` evaluates it on paths where `f` does not (the loop exits before reaching it). With a
symbol table lacking the symbol, `g` is `stuck` there and `f` returns: the per-function
simulation, which holds for every symbol table, is false, so every certificate is rejected.
The hoisting mode's theorem (`check_soundSyms`) assumes the symbol table resolves the
function's global values (`globalsResolve`), a property of the link-time image. -/

def shSv : Stmt := { results := [2], inst := .symbolValue .i64 0 }
def shB : Block := { id := 0, params := [(0, .i64), (1, .i64)], cold := false, body := [], term := br }
def shB' : Block := { id := 0, params := [(0, .i64), (1, .i64)], cold := false, body := [shSv], term := br }
def shB1 : Block := { id := 1, params := [], cold := false, body := [shSv], term := .ret [2] }
def shB1' : Block := { id := 1, params := [], cold := false, body := [], term := .ret [2] }
def shGv : List (Nat × GlobalValue) := [(0, .symbol "s" 0 false)]
def shF : Function := { name := "f", sig := sig3, globals := shGv, blocks := [shB, shB1, stB2] }
def shG : Function := { name := "f", sig := sig3, globals := shGv, blocks := [shB', shB1', stB2] }

theorem shF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\n    gv0 = symbol %s\nblock0(v0: i64, v1: i64):\n    brif v1, block1, block2\nblock1:\n    v2 = symbol_value.i64 gv0\n    return v2\nblock2:\n    return v0\n}" = some shF := by native_decide
theorem shG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\n    gv0 = symbol %s\nblock0(v0: i64, v1: i64):\n    v2 = symbol_value.i64 gv0\n    brif v1, block1, block2\nblock1:\n    return v2\nblock2:\n    return v0\n}" = some shG := by native_decide

/-- With `v1 = 0` and no symbols, `f` takes `block2` and returns, `g` is `stuck` on the
`symbol_value`. -/
theorem sh_not_sim : ¬ FunSimMU shF shG :=
  not_funSimMU_ret (b := shB) (b' := shB') (args := [⟨.i64, 0⟩, ⟨.i64, 0⟩]) (regs := hoRegs)
    (m := Mem.empty) (fr1 := ⟨shF, hoRegs, [], [], .ret [0]⟩) (vals := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl⟩

/-- The re-check rejects every certificate and every hint list for `neg_symhoist`. -/
theorem sh_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run shF) shG cert hints = false := by
  cases h : checkCertC (ConstPhi.run shF) shG cert hints
  · rfl
  · exact absurd (checkedC_simMU h) sh_not_sim

/-! ## Shared pieces of the store/load pairs -/

/-- One writable 8-byte allocation at address `0`, uninitialised. -/
def mem8 : Mem := { allocs := [{ base := 0, size := 8 }] }
/-- The same allocation holding zeros. -/
def mem8z : Mem := { allocs := [{ base := 0, size := 8 }], bytes := fun _ => some 0 }

/-- `v0 = 0` (the address), `v1 = 1`. -/
def regs01 : Regs := (Regs.empty.set 0 ⟨.i64, 0⟩).set 1 ⟨.i64, 1⟩
/-- `v0 = 0`, `v1 = 1`, `v2 = 2`. -/
def regs012 : Regs := ((Regs.empty.set 0 ⟨.i64, 0⟩).set 1 ⟨.i64, 1⟩).set 2 ⟨.i64, 2⟩

def p2 : List (ValueId × Ty) := [(0, .i64), (1, .i64)]
/-- `store.i64 v1, v0` -/
def st1 : Stmt := { results := [], inst := .store .store .i64 trapFl 1 0 0 }
/-- `store.i64 v2, v0` -/
def st2 : Stmt := { results := [], inst := .store .store .i64 trapFl 2 0 0 }
/-- `vr = load.i64 <fl> v0` -/
def ld (r : ValueId) (fl : MemFlags) : Stmt := { results := [r], inst := .load .load .i64 fl 0 0 }

/-! ## `neg_endian` -/

def enB : Block := { id := 0, params := p2, cold := false, body := [st1, ld 2 bigFl], term := .ret [2] }
def enB' : Block := { id := 0, params := p2, cold := false, body := [st1], term := .ret [1] }
def enF : Function := { name := "f", sig := sig3, blocks := [enB] }
def enG : Function := { name := "f", sig := sig3, blocks := [enB'] }

theorem enF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = load.i64 big v0\n    return v2\n}" = some enF := by native_decide
theorem enG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    return v1\n}" = some enG := by native_decide

theorem en_not_sim : ¬ FunSimMU enF enG :=
  not_funSimMU_ret_ne (b := enB) (b' := enB') (args := [⟨.i64, 0⟩, ⟨.i64, 1⟩]) (regs := regs01)
    (m := mem8) (vals := [⟨.i64, 0x0100000000000000⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.step rfl (.refl _ _)) rfl
    (by decide)

/-- The re-check rejects every certificate for `neg_endian`. -/
theorem en_rejected (cert : Cert) : checkCert (ConstPhi.run enF) enG cert = false := by
  cases h : checkCert (ConstPhi.run enF) enG cert
  · rfl
  · exact absurd (checked_simMU h) en_not_sim

/-! ## `neg_merge` -/

def p3 : List (ValueId × Ty) := [(0, .i64), (1, .i64), (2, .i64)]
def j3 : Terminator := .jump { block := 3, args := [] }
def mgB0 : Block :=
  { id := 0, params := p3, cold := false, body := [st1],
    term := .brif 2 { block := 1, args := [] } { block := 2, args := [] } }
def mgB1 : Block := { id := 1, params := [], cold := false, body := [st2], term := j3 }
def mgB2 : Block := { id := 2, params := [], cold := false, body := [], term := j3 }
def mgB3 : Block := { id := 3, params := [], cold := false, body := [ld 3 trapFl], term := .ret [3] }
def mgB3' : Block := { id := 3, params := [], cold := false, body := [], term := .ret [1] }
def mgF : Function := { name := "f", sig := sig4, blocks := [mgB0, mgB1, mgB2, mgB3] }
def mgG : Function := { name := "f", sig := sig4, blocks := [mgB0, mgB1, mgB2, mgB3'] }

theorem mgF_text : Pairs.fn? "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    store.i64 v2, v0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    v3 = load.i64 v0\n    return v3\n}" = some mgF := by native_decide
theorem mgG_text : Pairs.fn? "function %f(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n    store.i64 v1, v0\n    brif v2, block1, block2\nblock1:\n    store.i64 v2, v0\n    jump block3\nblock2:\n    jump block3\nblock3:\n    return v1\n}" = some mgG := by native_decide

theorem mg_not_sim : ¬ FunSimMU mgF mgG :=
  not_funSimMU_ret_ne (b := mgB0) (b' := mgB0) (args := [⟨.i64, 0⟩, ⟨.i64, 1⟩, ⟨.i64, 2⟩])
    (regs := regs012) (m := mem8) (vals := [⟨.i64, 2⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))))) rfl
    (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_merge`. -/
theorem mg_rejected (cert : Cert) : checkCert (ConstPhi.run mgF) mgG cert = false := by
  cases h : checkCert (ConstPhi.run mgF) mgG cert
  · rfl
  · exact absurd (checked_simMU h) mg_not_sim

/-! ## `neg_readonly` -/

def roB : Block :=
  { id := 0, params := p2, cold := false,
    body := [ld 2 roFl, st1, ld 3 roFl, { results := [4], inst := .binary .iadd .i64 2 3 }],
    term := .ret [4] }
def roB' : Block :=
  { id := 0, params := p2, cold := false,
    body := [ld 2 roFl, st1, { results := [4], inst := .binary .iadd .i64 2 2 }], term := .ret [4] }
def roF : Function := { name := "f", sig := sig3, blocks := [roB] }
def roG : Function := { name := "f", sig := sig3, blocks := [roB'] }

theorem roF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly v0\n    store.i64 v1, v0\n    v3 = load.i64 notrap readonly v0\n    v4 = iadd v2, v3\n    return v4\n}" = some roF := by native_decide
theorem roG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = load.i64 notrap readonly v0\n    store.i64 v1, v0\n    v4 = iadd v2, v2\n    return v4\n}" = some roG := by native_decide

theorem ro_not_sim : ¬ FunSimMU roF roG :=
  not_funSimMU_ret_ne (b := roB) (b' := roB') (args := [⟨.i64, 0⟩, ⟨.i64, 1⟩]) (regs := regs01)
    (m := mem8z) (vals := [⟨.i64, 1⟩]) (vals' := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_readonly`. -/
theorem ro_rejected (cert : Cert) : checkCert (ConstPhi.run roF) roG cert = false := by
  cases h : checkCert (ConstPhi.run roF) roG cert
  · rfl
  · exact absurd (checked_simMU h) ro_not_sim

/-! ## `neg_call` -/

def extG : ExtFunc :=
  { name := "g", sig := { params := [], returns := [], callConv := none }, colocated := false }
def callSt : Stmt := { results := [], inst := .call 0 [] }
def caB : Block :=
  { id := 0, params := p2, cold := false, body := [st1, callSt, ld 2 trapFl], term := .ret [2] }
def caB' : Block := { id := 0, params := p2, cold := false, body := [st1, callSt], term := .ret [1] }
def caF : Function := { name := "f", sig := sig3, externs := [(0, extG)], blocks := [caB] }
def caG : Function := { name := "f", sig := sig3, externs := [(0, extG)], blocks := [caB'] }

theorem caF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\n    fn0 = %g()\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    call fn0()\n    v2 = load.i64 v0\n    return v2\n}" = some caF := by native_decide
theorem caG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\n    fn0 = %g()\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    call fn0()\n    return v1\n}" = some caG := by native_decide

/-- The callee `%g` returns nothing and leaves the allocation zeroed (`mem8z`). -/
theorem ca_not_sim : ¬ FunSimMU caF caG :=
  not_funSimMU_call_ret (b := caB) (b' := caB') (args := [⟨.i64, 0⟩, ⟨.i64, 1⟩]) (regs := regs01)
    (m := mem8) (vs := []) (m' := mem8z) (vals := [⟨.i64, 0⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.refl _ _)) rfl (.step rfl (.refl _ _)) rfl rfl rfl rfl rfl
    (.step rfl (.refl _ _)) rfl (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_call`. -/
theorem ca_rejected (cert : Cert) : checkCert (ConstPhi.run caF) caG cert = false := by
  cases h : checkCert (ConstPhi.run caF) caG cert
  · rfl
  · exact absurd (checked_simMU h) ca_not_sim

/-! ## `neg_type`: a simulation the checker rejects (module doc) -/

def tyB : Block :=
  { id := 0, params := p2, cold := false,
    body := [st1, { results := [2], inst := .load .load .i32 trapFl 0 0 },
      { results := [3], inst := .extend .uextend .i64 2 }],
    term := .ret [3] }
def tyB' : Block :=
  { id := 0, params := p2, cold := false,
    body := [st1, { results := [2], inst := .ireduce .i32 1 },
      { results := [3], inst := .extend .uextend .i64 2 }],
    term := .ret [3] }
def tyF : Function := { name := "f", sig := sig3, blocks := [tyB] }
def tyG : Function := { name := "f", sig := sig3, blocks := [tyB'] }

theorem tyF_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = load.i32 v0\n    v3 = uextend.i64 v2\n    return v3\n}" = some tyF := by native_decide
theorem tyG_text : Pairs.fn? "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    store.i64 v1, v0\n    v2 = ireduce.i32 v1\n    v3 = uextend.i64 v2\n    return v3\n}" = some tyG := by native_decide

/-- The executable check rejects `neg_type` (decided by `native_decide`), although `g` simulates
`f` on the little-endian memory (module doc): the checker does not forward a narrower load from a
wider store. -/
theorem ty_check_rejects : ∃ e, Opt.MidVal.check (ConstPhi.run tyF) tyG = .error e := by
  have h : (Opt.MidVal.check (ConstPhi.run tyF) tyG).isOk = false := by native_decide
  revert h
  cases Opt.MidVal.check (ConstPhi.run tyF) tyG with
  | ok _ => intro h; cases h
  | error e => intro _; exact ⟨e, rfl⟩

end Opt.MidVal.NegWitness
