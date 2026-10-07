import FV.E2E.LinkArm
import FV.Opt.Legalize128Pass
import FV.E2E.Legal

/-! # Non-vacuity of `backend_correct_program` (docs/contracts/e2e.md, "Non-vacuity")

A concrete linked program for which every premise of `E2E.backend_correct_program` holds:
`P = {f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y, z}`, parsed from the embedded source
`src`, legalised (`Opt.Legalize128.parsedFile128`), compiled by the
backend's pipeline (`lowerFunction`, `prepare`, regalloc2's allocation `raOut` — the output of
`lean-regalloc` on the pipeline's input for this file, rebuilt by `buildRFunc` and accepted by
`checkAlloc` —, `lowerRFunc`, `emitFunc`, `layout`), loaded at `0x70000` (`f`), `0x20000`,
`0x10000`, `0x30000`, `0x40000`, `0x50000` (`r` and `r__fvself`: one copy), `0x80000`…`0xF0000`,
`0xF4000` (`e`), `0xF6000` (`y`), `0xF7000` (`z`). The entry `f` has a
stack slot and an outgoing-argument area; it calls

* `s` with an `sret` pointer to its slot (`s` stores through it, returns the pointer in x0),
* `k` with 9 arguments (the 9th on the stack, in `f`'s outgoing area),
* `g` by a `try_call` with a result (`g` calls `h`: a non-leaf program callee),
* the recursive `r` (`r n = 2 n`): its self-call is `cargo fv`'s alias `r__fvself`, a second
  function with `r`'s body whose self-call names `r` (the two call each other), compiled to the
  same words and loaded at `r`'s address: one copy of the code, each call returning into the
  callee's own code (`raCall`'s second case, `RaOk`),
* `v`, which calls `q` (`q n = n + 5`) through a pointer (`func_addr`, `call_indirect`: a `blr`
  the linked machine resolves by the address in its register) and through the GOT (`blr`),
* `w`, which passes two `i128` values to `a2` (`i128` addition) and adds the halves of its result:
  `a2` and `w` are legalised (`i128` pairs in x0–x3, the result in x0/x1); `a2_legal` composes
  `a2`'s linked code with `backend_correct_legal` against the `i128` source,
* `t`, a callee with a stack slot (`t n = 2 n + 10`: it stores `n + 10` through `stack_addr` and
  loads it back), placed by the slot-placement oracle at its compiled frame address,
* `u`, a callee with an outgoing-argument area (`u n = 1 + n`: it passes `n` to `k` on the stack),
* `d` with the address of the vtable `vt` (`symbol_value`): a `cg_clif`-style trait-object
  vtable, a read-only data object whose second word is a relocation to the method `m`
  (`m n = n + 11`); `d` loads the method from the vtable and calls it (`call_indirect`) without
  declaring `m` — the linked environment resolves the address program-wide.

`P` also contains `e` (not called by `f`): it calls the base extern `pz` through the GOT (`blr`,
arguments in x0/x1) next to the declared program function `s` of the same register arity (its
`sret` pointer in x8, its argument in x0; one ABI result). The `blr` site's target is `pz`'s GOT
entry (`GotV`), so it constrains no function of `P` (`LinkSys.BlrTo`); the former `blrRegs`,
which quantified over every declared function of that arity, failed on it. `P` also contains `y`
(not called by `f`): it calls the pointer it is passed (`call_indirect`, signature
`(i64, i32) -> i32`, arguments in x0/x1) next to `s`, which has an address (its `sret`
pointer in x8, its argument in x0); no indirect call of `y` matches `s`'s signature, so the
`blr` constrains only the functions it can enter (`LinkSys.IndTo`); a `blrRegs` over every
function with an address failed on it. `P` also contains `z` (not called by `f`): it calls the
pointer it is passed with the signature `(i64, i64)` (arguments in x0/x1), which has the
parameter types of `s` (`(i64 sret, i64)`) but not its parameter purposes. `Clif.stepCallIndirect`
enters a function only when the call-site signature matches its own, purposes included
(`Clif.Signature.abiMatch`, Cranelift's "the called function must match the specified
signature"), so `z` cannot reach `s` (`LinkSys.MayCall`), and neither `indSig` nor `blrRegs`
constrains `s` at `z`'s calls. With the former type-only matching, `indSig` (`s` takes an
`sret` pointer) and `blrRegs` (x8/x0 against the call's x0/x1) both failed on it.

* The per-function premises of `LinkSys.Ok` are executable checks (`chks`, `okB`, each with a
  soundness lemma: `siteOk_sound`, `retsB_sound`, `outFitsB_sound`,
  `entryB_sound`, `raCallB_sound`, `linkFreeB_sound`, `imgCode_of`, …), decided by
  `native_decide` (`okB_true`; the project's axiom policy allows `_native.native_decide` axioms).
* The base environment is closed: no extern outside `P` (`Xb.call` undefined, so `baseNI` holds
  vacuously), calls outside `P` continue at the next instruction (`Hb`), no TLS (the TLSDESC flags
  are the world's `pstate`: `baseTlsNI`).
* **`L_ok`**: `(L F).Ok` for every `F` containing the code. `t` and `u` make the premises gated by
  `NeedSlots` and `NeedNI` non-vacuous.
* **`backend_correct_program_witness`**: with the entry premises of `f` on the argument `41`
  (ABI entry state `s0`, body-entry world `w0`, CLIF entry state `cs0` with `f`'s slot at its
  frame address and the slot-placement oracle at the body's `sp`), the theorem applies: the
  linked machine refines `f`'s CLIF run, which returns `802`.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

def src : String := "function %h(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = iadd v0, v1
    return v2
}

function %g(i64) -> i64 system_v {
    fn0 = colocated %h(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    v2 = iadd v1, v0
    return v2
}

function %s(i64 sret, i64) system_v {
block0(v0: i64, v1: i64):
    v2 = iconst.i64 7
    v3 = iadd v1, v2
    store.i64 notrap aligned v3, v0
    return
}

function %k(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64):
    v9 = iadd v0, v8
    return v9
}

function %r(i64) -> i64 system_v {
    fn0 = colocated %r__fvself(i64) -> i64 system_v
block0(v0: i64):
    brif v0, block1, block2
block1:
    v1 = iconst.i64 1
    v2 = isub v0, v1
    v3 = call fn0(v2)
    v4 = iconst.i64 2
    v5 = iadd v3, v4
    return v5
block2:
    v6 = iconst.i64 0
    return v6
}

function %r__fvself(i64) -> i64 system_v {
    fn0 = colocated %r(i64) -> i64 system_v
block0(v0: i64):
    brif v0, block1, block2
block1:
    v1 = iconst.i64 1
    v2 = isub v0, v1
    v3 = call fn0(v2)
    v4 = iconst.i64 2
    v5 = iadd v3, v4
    return v5
block2:
    v6 = iconst.i64 0
    return v6
}

function %f(i64) -> i64 system_v {
    ss0 = explicit_slot 8
    gv0 = symbol colocated %vt
    sig0 = (i64) -> i64 system_v
    fn0 = colocated %g(i64) -> i64 system_v
    fn1 = colocated %s(i64 sret, i64) system_v
    fn2 = colocated %k(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v
    fn3 = colocated %r(i64) -> i64 system_v
    fn4 = colocated %v(i64) -> i64 system_v
    fn5 = colocated %w(i64) -> i64 system_v
    fn6 = colocated %t(i64) -> i64 system_v
    fn7 = colocated %u(i64) -> i64 system_v
    fn8 = colocated %d(i64, i64) -> i64 system_v
block0(v0: i64):
    v1 = stack_addr.i64 ss0
    call fn1(v1, v0)
    v2 = load.i64 notrap aligned v1
    v3 = iconst.i64 0
    v4 = call fn2(v2, v3, v3, v3, v3, v3, v3, v3, v0)
    try_call fn0(v4), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v5: i64):
    v7 = iconst.i64 3
    v8 = call fn3(v7)
    v9 = iadd v5, v8
    v10 = call fn4(v9)
    v11 = call fn5(v10)
    v12 = call fn6(v11)
    v13 = call fn7(v12)
    v14 = symbol_value.i64 gv0
    v15 = call fn8(v14, v13)
    return v15
block2(v6: i64):
    return v6
}

function %q(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 5
    v2 = iadd v0, v1
    return v2
}

function %v(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = colocated %q(i64) -> i64 system_v
    fn1 = %q(i64) -> i64 system_v
block0(v0: i64):
    v1 = func_addr.i64 fn0
    v2 = call_indirect sig0, v1(v0)
    v3 = call fn1(v2)
    return v3
}

function %a2(i128, i128) -> i128 system_v {
block0(v0: i128, v1: i128):
    v2 = iadd v0, v1
    return v2
}

function %w(i64) -> i64 system_v {
    fn0 = colocated %a2(i128, i128) -> i128 system_v
block0(v0: i64):
    v1 = uextend.i128 v0
    v2 = call fn0(v1, v1)
    v3, v4 = isplit v2
    v5 = iadd v3, v4
    return v5
}

function %t(i64) -> i64 system_v {
    ss0 = explicit_slot 8
block0(v0: i64):
    v1 = stack_addr.i64 ss0
    v2 = iconst.i64 10
    v3 = iadd v0, v2
    store.i64 notrap aligned v3, v1
    v4 = load.i64 notrap aligned v1
    v5 = iadd v4, v0
    return v5
}

function %u(i64) -> i64 system_v {
    fn0 = colocated %k(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = call fn0(v1, v1, v1, v1, v1, v1, v1, v1, v0)
    return v2
}

function %m(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 11
    v2 = iadd v0, v1
    return v2
}

function %d(i64, i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
block0(v0: i64, v1: i64):
    v2 = load.i64 notrap aligned readonly v0+8
    v3 = call_indirect sig0, v2(v1)
    return v3
}

function %e(i64, i64) -> i64 system_v {
    fn0 = colocated %s(i64 sret, i64) system_v
    fn1 = %pz(i64, i64) system_v
block0(v0: i64, v1: i64):
    brif v1, block1, block2
block1:
    call fn1(v1, v0)
    return v1
block2:
    call fn0(v0, v1)
    return v1
}

function %y(i64, i64, i32) -> i32 system_v {
    sig0 = (i64, i32) -> i32 system_v
block0(v0: i64, v1: i64, v2: i32):
    v3 = call_indirect sig0, v0(v1, v2)
    return v3
}

function %z(i64, i64, i64) system_v {
    sig0 = (i64, i64) system_v
block0(v0: i64, v1: i64, v2: i64):
    call_indirect sig0, v0(v1, v2)
    return
}
"

def raOut : String := "{\"functions\":[{\"allocs\":[[\"x0\"],[\"x2\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"h\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\",\"x19\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x19\"}],\"name\":\"g\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x8\",\"x0\"],[\"x3\"],[\"x5\",\"x0\"],[\"x5\",\"x8\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x8\",\"inst\":4,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"s\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\",\"x2\",\"x3\",\"x4\",\"x5\",\"x6\",\"x7\"],[\"x9\"],[\"x0\",\"x0\",\"x9\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"k\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\"],[\"x0\"],[\"x0\"],[\"x5\"],[\"x0\",\"x0\"],[\"x0\",\"x0\"],[\"x11\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"r\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\"],[\"x0\"],[\"x0\"],[\"x5\"],[\"x0\",\"x0\"],[\"x0\",\"x0\"],[\"x11\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"r__fvself\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x8\"],[\"x8\",\"x0\",\"x0\"],[\"x0\"],[\"x7\"],[\"x21\"],[\"x0\",\"x1\",\"x2\",\"x3\",\"x4\",\"x5\",\"x6\",\"x7\",\"x0\"],[\"x0\",\"x0\",\"x1\"],[],[\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x1\",\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\"],[\"x0\"],[\"x0\",\"x1\",\"x0\"],[\"x0\"],[],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":2,\"pos\":\"before\",\"to\":\"x21\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x2\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x3\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x4\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x5\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x6\"},{\"from\":\"x0\",\"inst\":8,\"pos\":\"before\",\"to\":\"x25\"},{\"from\":\"x25\",\"inst\":11,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x0\",\"inst\":16,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x0\",\"inst\":19,\"pos\":\"before\",\"to\":\"x25\"},{\"from\":\"x25\",\"inst\":20,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"f\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x2\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"q\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x2\"],[\"x2\",\"x0\",\"x0\"],[\"x7\"],[\"x7\",\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"v\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\",\"x2\",\"x3\"],[\"x5\"],[\"x7\",\"x0\",\"x2\"],[\"x7\",\"x0\"],[\"x10\"],[\"x7\",\"x0\"],[\"x13\"],[\"x15\",\"x1\",\"x3\"],[\"x1\",\"x15\",\"x10\"],[\"x0\",\"x1\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x7\",\"inst\":9,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"a2\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x2\"],[\"x2\",\"x0\",\"x0\"],[\"x3\"],[\"x0\",\"x1\",\"x2\",\"x3\",\"x0\",\"x1\"],[\"x11\",\"x0\",\"x0\"],[\"x13\",\"x1\",\"x1\"],[\"x0\",\"x11\",\"x13\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x2\",\"inst\":4,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x3\",\"inst\":4,\"pos\":\"before\",\"to\":\"x1\"}],\"name\":\"w\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x2\"],[\"x4\"],[\"x6\",\"x0\"],[\"x6\"],[\"x9\"],[\"x0\",\"x9\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"t\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x7\"],[\"x0\"],[\"x0\",\"x1\",\"x2\",\"x3\",\"x4\",\"x5\",\"x6\",\"x7\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x2\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x3\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x4\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x5\"},{\"from\":\"x7\",\"inst\":3,\"pos\":\"before\",\"to\":\"x6\"}],\"name\":\"u\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x2\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"m\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\"],[\"x3\",\"x0\"],[\"x3\",\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x1\",\"inst\":2,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"d\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\"],[\"x1\"],[\"x8\",\"x0\",\"x0\"],[\"x0\"],[\"x6\"],[\"x6\",\"x0\",\"x1\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x8\"},{\"from\":\"x1\",\"inst\":2,\"pos\":\"before\",\"to\":\"x19\"},{\"from\":\"x19\",\"inst\":2,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x19\",\"inst\":3,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x1\",\"inst\":4,\"pos\":\"before\",\"to\":\"x19\"},{\"from\":\"x8\",\"inst\":5,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x19\",\"inst\":5,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x19\",\"inst\":6,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"e\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\",\"x2\"],[\"x7\",\"x0\",\"x1\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x7\"},{\"from\":\"x1\",\"inst\":1,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x2\",\"inst\":1,\"pos\":\"before\",\"to\":\"x1\"}],\"name\":\"y\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\",\"x2\"],[\"x6\",\"x0\",\"x1\"],[]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x6\"},{\"from\":\"x1\",\"inst\":1,\"pos\":\"before\",\"to\":\"x0\"},{\"from\":\"x2\",\"inst\":1,\"pos\":\"before\",\"to\":\"x1\"}],\"name\":\"z\",\"num_spillslots\":0,\"ok\":true}]}"

deriving instance Inhabited for Art

def getOk {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => default

theorem getOk_eq {ε α : Type} [Inhabited α] {x : Except ε α} (h : x.toBool = true) :
    x = .ok (getOk x) := by
  cases x <;> simp_all [getOk, Except.toBool]

/-- Function `i` of the file as the backend compiles it: legalised (`Opt.Legalize128`, the
identity on the functions without `i128`). -/
def fn (i : Nat) : Clif.Function :=
  match (Opt.Legalize128.parsedFile128 (Clif.parseFile src)).file.funcs[i]? with
  | some p => getOk p.func
  | none => default

def fH : Clif.Function := fn 0
def fG : Clif.Function := fn 1
def fS : Clif.Function := fn 2
def fK : Clif.Function := fn 3
def fR : Clif.Function := fn 4
/-- `r`'s alias (`cargo fv`'s `r__fvself`): `r`'s body, its self-call naming `r`. -/
def fRS : Clif.Function := fn 5
def fF : Clif.Function := fn 6
def fQ : Clif.Function := fn 7
/-- `v` calls `q` through a pointer (`func_addr`, `call_indirect`) and through the GOT. -/
def fV : Clif.Function := fn 8
/-- The legalisation of `a2 : (i128, i128) -> i128`: `(i64, i64, i64, i64) -> (i64, i64)`. -/
def fA2 : Clif.Function := fn 9
/-- The legalisation of `w`, which passes `i128` pairs to `a2` and splits its `i128` result. -/
def fW : Clif.Function := fn 10
/-- A callee with a stack slot, written and read through `stack_addr`. -/
def fT : Clif.Function := fn 11
/-- A callee with an outgoing-argument area: it passes a stack argument to `k`. -/
def fU : Clif.Function := fn 12
/-- The trait method `m` (`m n = n + 11`), reached only through the vtable `vt`. -/
def fM : Clif.Function := fn 13
/-- The `dyn` dispatcher `d`: it loads the method from the vtable and calls it
(`call_indirect`); it declares nothing. -/
def fD : Clif.Function := fn 14
/-- `e` calls the base extern `pz` through the GOT (`blr`, two register arguments in x0/x1) next
to the declared program function `s` of the same arity with a result (its `sret` pointer in x8,
returned in x0): the GOT site's target is `pz`, not `s` (`GotV`). -/
def fE : Clif.Function := fn 15
/-- `y` calls the pointer it is passed (`call_indirect`, signature `(i64, i32) -> i32`): it may
reach `s` (which has an address), whose argument registers differ from the call's, but no
indirect call of `y` has `s`'s parameter types (`LinkSys.IndTo`). -/
def fY : Clif.Function := fn 16
/-- `z` calls the pointer it is passed (`call_indirect`, signature `(i64, i64)`): the parameter
types of `s` (`(i64 sret, i64)`) but not its parameter purposes, so it cannot reach `s`. -/
def fZ : Clif.Function := fn 17

/-- Function `i` of the file as written (before legalisation). -/
def srcFn (i : Nat) : Clif.Function := match (Clif.parseFile src).funcs[i]? with
  | some p => getOk p.func
  | none => default

/-- The legalisation certificate of function `i`. -/
def certOf (i : Nat) : Opt.Legalize128.Cert :=
  (getOk (Opt.Legalize128.function128Cert (srcFn i))).2

def raJ (i : Nat) : Lean.Json :=
  (((getOk (Lean.Json.parse raOut)).getObjVal? "functions").bind (·.getArr?)).toOption.getD #[] |>.getD i default

/-- The pipeline on function `i` of `src` with index `k` and load address `base`. -/
def pipe (f : Clif.Function) (k : Nat) (base : BitVec 64) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare vc
  let o ← parseRAOut (raJ k)
  let rf ← buildRFunc vcp o
  let af ← lowerRFunc vcp rf
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, rf, af, fa, fb, base⟩


/-! ## The program and its compiled image -/

/-- The program `{f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y, z}`. -/
def P : Clif.Program :=
  { funcs := [fF, fG, fH, fS, fK, fR, fRS, fQ, fV, fA2, fW, fT, fU, fM, fD, fE, fY, fZ] }

/-- The file index of a function of `P` (the regalloc2 output and the local labels). -/
def idx (g : Clif.Function) : Nat :=
  if g = fF then 6 else if g = fG then 1 else if g = fS then 2 else if g = fK then 3
  else if g = fR then 4 else if g = fRS then 5 else if g = fQ then 7 else if g = fV then 8
  else if g = fA2 then 9 else if g = fW then 10 else if g = fT then 11 else if g = fU then 12
  else if g = fM then 13 else if g = fD then 14 else if g = fE then 15 else if g = fY then 16
  else if g = fZ then 17 else 0

/-- The load address of a function of `P` (`e`, `y` and `z` between `d` and the vtable;
`r__fvself` at `r`'s address: one copy of their code). -/
def baseOf (g : Clif.Function) : BitVec 64 :=
  if idx g = 15 then 0xF4000 else if idx g = 16 then 0xF6000 else if idx g = 17 then 0xF7000
  else if idx g = 5 then 0x50000
  else 0x10000 * BitVec.ofNat 64 (idx g + 1)

/-- The compiled image of every function. -/
def A (g : Clif.Function) : Art := getOk (pipe g (idx g) (baseOf g))

theorem pipe_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {a : Art}
    (h : pipe f k base = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipe at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : parseRAOut (raJ k) with _ | o <;> simp only [h3] at h
  · cases h
  rcases h4 : buildRFunc vcp o with _ | rf <;> simp only [h4] at h
  · cases h
  rcases h5 : lowerRFunc vcp rf with _ | af <;> simp only [h5] at h
  · cases h
  rcases h6 : emitFunc k af with _ | fa <;> simp only [h6] at h
  · cases h
  rcases h7 : fa.layout with _ | fb <;> simp only [h7] at h
  · cases h
  cases h
  exact ⟨rfl, h2, h5, h6, h7, rfl, rfl⟩

/-! ## Executable checks of the premises -/

/-- Every instruction of `vc` satisfies `p`. -/
def allInsts (vc : VCode) (p : MInst → Bool) : Bool := vc.blocks.all fun vb => vb.insts.all p

theorem allInsts_sound {vc : VCode} {p : MInst → Bool} (h : allInsts vc p = true) {b k : Nat}
    {vb : VBlock} {i : MInst} (hb : vc.blocks[b]? = some vb) (hk : vb.insts[k]? = some i) :
    p i = true :=
  (array_all_iff _ _).1 ((array_all_iff _ _).1 h b vb hb) k i hk

/-- `q` at every call site. -/
def siteB (q : CallInfo → Bool) : MInst → Bool
  | .call info => q info
  | .tryCall info _ => q info
  | _ => true

theorem site_sound {vc : VCode} {q : CallInfo → Bool} (h : allInsts vc (siteB q) = true)
    {info : CallInfo} (hs : vc.CallSite info) : q info = true := by
  obtain ⟨b, vb, k, hb, hk | ⟨ti, hk⟩⟩ := hs
  · simpa [siteB] using allInsts_sound h hb hk
  · simpa [siteB] using allInsts_sound h hb hk

def decU (us : List (Reg × Reg)) : List (Nat × Reg) :=
  us.map fun p => ((match p.1 with | .vreg n _ => n | _ => 0), p.2)

def decD (ds : List (Reg × Reg)) : List (Reg × Nat) :=
  ds.map fun p => (p.1, match p.2 with | .vreg n _ => n | _ => 0)

/-- `g` declares `n`, other than itself (`DeclN`). -/
def declB (g : Clif.Function) (n : String) : Bool :=
  g.externs.any (fun e => e.2.name == n) && n != g.name

theorem declB_sound {g : Clif.Function} {n : String} (h : declB g n = true) : DeclN g n := by
  simp only [declB, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨e, he, hn⟩, hne⟩ := h
  exact ⟨List.mem_map.mpr ⟨e, he, hn⟩, hne⟩

theorem declB_of {g : Clif.Function} {n : String} (h : DeclN g n) : declB g n = true := by
  obtain ⟨hm, hne⟩ := h
  obtain ⟨e, he, hen⟩ := List.mem_map.mp hm
  simp only [declB, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨e, he, hen⟩, hne⟩

/-- A `blr` site: arguments in the parameter registers, of every function of `P` it may enter
(`LinkSys.BlrTo`: one the caller may enter through an address, `may`, and at a call through the
GOT, `got`, the GOT
symbol's) with as many register parameters, and the results its defs hold from x0... -/
def blrOk (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String) (info : CallInfo) :
    Bool :=
  match info.dest with
  | .reg (.vreg t .int) =>
    decide (info.uses = retPairs (decU info.uses)) &&
    decide (info.defs = callDefs (decD info.defs)) &&
    P.funcs.all fun h => !may h ||
      (match got t with | some n => h.name != n | none => false) ||
      decide ((regLocs h.sig).length ≠ (decU info.uses).length) ||
      (decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x))
  | _ => false

theorem blrOk_sound {P : Clif.Program} {may : Clif.Function → Bool} {got : Nat → Option String}
    {info : CallInfo} (h : blrOk P may got info = true) :
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) →
        (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold blrOk at h
  split at h
  · rename_i t hd
    simp only at hd
    subst hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨hu, hd⟩, hall⟩ := h
    refine ⟨t, decU us, decD ds, by rw [← hu, ← hd], fun h' hh hmay hgot hl => ?_⟩
    rcases hall h' hh with ((h1 | h1) | h1) | h1
    · rw [hmay] at h1; cases h1
    · revert h1
      cases hg : got t with
      | none => simp
      | some n => simp [hgot n hg]
    · exact absurd hl h1
    · exact h1
  · cases h

/-- A call site: a `bl` of a function `h` of `P` that `g` declares, arguments in `h`'s parameter
registers, results from x0.. (then, at a `try_call`, the exception payload registers); or a
`blr` site (`blrOk`). -/
def siteOk (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => decide (h ≠ g) && g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => false
  | .reg _ => blrOk P may (gotOf vc) info

theorem siteOk_reg {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool} {vc : VCode}
    {info : CallInfo} (h : siteOk P g may vc info = true) (hd : ∀ n, info.dest ≠ .sym n) :
    blrOk P may (gotOf vc) info = true := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => exact h
  | sym n => exact absurd rfl (hd n)

theorem siteOk_sound {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool} {vc : VCode}
    {info : CallInfo} (h : siteOk P g may vc info = true) {n0 : String} (hd0 : info.dest = .sym n0) :
    ∃ n h', info.dest = .sym n ∧ P.func? n = some h' ∧ h' ≠ g ∧
      (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      (Ld.map (·.1)).take (sigRets h'.sig).length =
        (List.range (min (sigRets h'.sig).length Ld.length)).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => cases hd0
  | sym n =>
    cases hf : P.func? n with
    | none => simp [hf] at h
    | some h' =>
      simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨hne, hd⟩, hu⟩, hdd⟩, h1⟩, h2⟩ := h
      exact ⟨n, h', rfl, hf, hne, hd, _, _, by rw [← hu, ← hdd], h1, h2⟩

/-- The returns of an `sret` function carry its ABI results. -/
def retsB (g : Clif.Function) : MInst → Bool
  | .rets us => !(g.sig.params.any (·.purpose == .sret)) || decide ((sigRets g.sig).length ≤ us.length)
  | _ => true

theorem retsB_sound {g : Clif.Function} {vc : VCode} (h : allInsts vc (retsB g) = true)
    (hs : g.sig.params.any (·.purpose == .sret) = true) {us : List (Reg × Reg)}
    (hr : vc.RetsSite us) : (sigRets g.sig).length ≤ us.length := by
  obtain ⟨b, vb, k, hb, hk⟩ := hr
  have := allInsts_sound h hb hk
  simpa [retsB, hs] using this

/-- The stack-passed parameters of `sig` fit an outgoing area of `ib` bytes. -/
def outFitsB (sig : Clif.Signature) (ib : Nat) : Bool :=
  (List.range (locsOf sig).length).all fun i => match (locsOf sig)[i]?, sig.params[i]? with
    | some (.stack off), some p => decide (off + p.ty.bytes ≤ ib)
    | _, _ => true

theorem outFitsB_sound {sig : Clif.Signature} {ib : Nat} (h : outFitsB sig ib = true) {i off : Nat}
    {p : Clif.AbiParam} (hl : (locsOf sig)[i]? = some (.stack off)) (hp : sig.params[i]? = some p) :
    off + p.ty.bytes ≤ ib := by
  have hi : i < (locsOf sig).length := (List.getElem?_eq_some_iff.mp hl).1
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa [hl, hp] using this

/-- The entry `Args` reads parameter registers. -/
def entryB (g : Clif.Function) (vc : VCode) : Bool :=
  match vc.blocks[0]? with
  | some vb => match vb.insts[0]? with
    | some (MInst.args ds) => ds.all fun p => decide (p.2 ∈ regLocs g.sig)
    | _ => true
  | none => true

theorem entryB_sound {g : Clif.Function} {vc : VCode} (h : entryB g vc = true) {r : Reg}
    (hr : vc.EntryArg r) : r ∈ regLocs g.sig := by
  obtain ⟨vb, ds, hb, hi, v, hv⟩ := hr
  simp only [entryB, hb, hi, List.all_eq_true, decide_eq_true_eq] at h
  exact h _ hv

/-- No `return_call`. -/
def linkFreeB (g : Clif.Function) : Bool :=
  g.blocks.all fun b => match b.term with | .returnCall .. => false | _ => true

theorem linkFreeB_sound {g : Clif.Function} (h : linkFreeB g = true) : Clif.LinkFree g := by
  intro b hb fn args he
  simp only [linkFreeB, List.all_eq_true] at h
  have := h b hb
  rw [he] at this; simp at this

/-- No `call_indirect`, `try_call_indirect`. -/
def indFreeB (g : Clif.Function) : Bool :=
  g.blocks.all fun b =>
    b.body.all (fun st => match st.inst with | .callIndirect .. => false | _ => true) &&
    (match b.term with | .tryCallIndirect .. => false | _ => true)

theorem indFreeB_of {g : Clif.Function} (h : Clif.IndFree g) : indFreeB g = true := by
  simp only [indFreeB, List.all_eq_true, Bool.and_eq_true]
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨fun st hst => ?_, ?_⟩
  · split
    · rename_i sig c a e
      exact absurd e (h1 st hst sig c a)
    · rfl
  · split
    · rename_i c a et e
      exact absurd e (h2 c a et)
    · rfl

theorem indFreeB_sound {g : Clif.Function} (h : indFreeB g = true) : Clif.IndFree g := by
  intro b hb
  simp only [indFreeB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨fun st hst sig callee args he => ?_, fun callee args et he => ?_⟩
  · have := h1 st hst; rw [he] at this; simp at this
  · rw [he] at h2; simp at h2

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → b ∈ l.map (·.2)
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- The call instructions of the laid-out code. -/
def callLine : Line → Bool
  | .ins (.bl _) _ => true
  | .ins (.blr _) _ => true
  | _ => false

/-- `LinkSys.RaOk` decided: the return address of the call at `pc` is outside `ah`'s code, or
after a call instruction of `ah`'s code and not at its entry. -/
def raOkB (ah : Art) (pc : BitVec 64) : Bool :=
  (List.range ah.fb.words.size).all (fun k => pc + 4 != ah.base + BitVec.ofNat 64 (4 * k)) ||
  (pc + 4 != ah.base && (List.range ah.fa.lines.toList.length).any fun j =>
    match ah.fa.lines.toList[j]? with
    | some l => callLine l && pc == ah.base + BitVec.ofNat 64 (lineOffset ah.fa.lines.toList j)
    | none => false)

theorem raOkB_sound {ah : Art} {pc : BitVec 64} (h : raOkB ah pc = true) : RaOk ah pc := by
  simp only [raOkB, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨hne, j, -, hl⟩
  · exact .inl fun k hk => h k hk
  · refine .inr ⟨?_, hne⟩
    revert hl
    cases e : ah.fa.lines.toList[j]? with
    | none => simp
    | some l =>
      intro hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      obtain ⟨hc, rfl⟩ := hl
      cases l with
      | ins i t =>
        cases i <;> simp only [callLine, Bool.false_eq_true] at hc
        · exact ⟨j, _, t, e, .inl ⟨_, rfl⟩, rfl⟩
        · exact ⟨j, _, t, e, .inr ⟨_, rfl⟩, rfl⟩
      | _ => simp [callLine] at hc

/-- The return address of every call of `a` (the code of `g`) is not `a`'s entry, and is outside
the code of every other function of `P`, or after a call of that function's code (`raOkB`). -/
def raCallB (P : Clif.Program) (A : Clif.Function → Art) (g : Clif.Function) (a : Art) : Bool :=
  let ls := a.fa.lines.toList
  (List.range ls.length).all fun j =>
    match ls[j]? with
    | some l => !callLine l || (a.base + BitVec.ofNat 64 (lineOffset ls j) + 4 != a.base &&
        P.funcs.all fun h => decide (h = g) ||
          raOkB (A h) (a.base + BitVec.ofNat 64 (lineOffset ls j)))
    | none => true

theorem raCallB_parts {P : Clif.Program} {A : Clif.Function → Art} {g : Clif.Function} {a : Art}
    (h : raCallB P A g a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) :
    pc + 4 ≠ a.base ∧ ∀ h' ∈ P.funcs, h' ≠ g → RaOk (A h') pc := by
  obtain ⟨j, i, t, hj, hi, rfl⟩ := hpc
  have hjl : j < a.fa.lines.toList.length := (List.getElem?_eq_some_iff.1 hj).1
  simp only [raCallB, List.all_eq_true, List.mem_range] at h
  have := h j hjl
  rw [hj] at this
  have hc : callLine (.ins i t) = true := by
    rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, fun h' hh hne => raOkB_sound ((this.2 h' hh).resolve_left hne)⟩

theorem raCallB_sound {P : Clif.Program} {A : Clif.Function → Art} {g : Clif.Function} {a : Art}
    (h : raCallB P A g a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) :
    ∀ h' ∈ P.funcs, h' ≠ g → RaOk (A h') pc :=
  (raCallB_parts h hpc).2

def raStarB (P : Clif.Program) (A : Clif.Function → Art) (ra : BitVec 64) : Bool :=
  P.funcs.all fun h => let ah := A h
    (List.range ah.fb.words.size).all fun k => ra != ah.base + BitVec.ofNat 64 (4 * k)

/-! ## The code image -/

/-- The words of every function at its base. -/
def progAll (P : Clif.Program) (A : Clif.Function → Art) : Arm.Program :=
  P.funcs.flatMap fun g => (A g).fb.program (A g).base

/-- The bytes of a list of code words. -/
def memOf (prog : Arm.Program) : Arm.Memory := fun a =>
  match List.find? (fun (p : BitVec 64 × BitVec 32) => decide ((a - p.1).toNat < 4)) prog with
  | some p => p.2.extractLsb' (8 * (a - p.1).toNat) 8
  | none => 0

/-- The code addresses of the functions of `P`. -/
def Img (P : Clif.Program) (A : Clif.Function → Art) (a : BitVec 64) : Prop :=
  ∃ g ∈ P.funcs, CodeAddr (Arm.set_program Arm.ArmState.default ((A g).fb.program (A g).base)) a

/-- The image read back word by word. -/
def imgB (P : Clif.Program) (A : Clif.Function → Art) : Bool :=
  P.funcs.all fun g => let a := A g
    (List.range a.fb.words.size).all fun k =>
      Arm.read_mem_bytes 4 (a.base + BitVec.ofNat 64 (4 * k))
        (setMem Arm.ArmState.default (memOf (progAll P A))) == a.fb.words[k]!

/-- The address of the vtable `vt` (a data object, after the code). -/
def vtAddr : Nat := 0xF8000

/-- The link-time addresses of the CLIF image: `q` (the function `v` calls through a pointer),
`m` (the method in the vtable), `k` (a function with a stack-passed parameter, whose signature
no indirect call has) and `s` (an `sret` function: arguments in x8, x0) at their bases, and the
vtable `vt`. -/
def symsW (n : String) : Option Nat :=
  if n = "q" then some 0x80000 else if n = "m" then some 0xE0000
  else if n = "vt" then some vtAddr else if n = "k" then some 0x40000
  else if n = "s" then some 0x30000 else none

/-- `g` may call `n` (an over-approximation of `LinkSys.MayCall` of the witness): declared, or
with an address when `g` has indirect calls. -/
def mayB (g : Clif.Function) (n : String) : Bool :=
  declB g n || (!indFreeB g && (symsW n).isSome)

/-- `g` may enter `h` through an address (an over-approximation of `LinkSys.IndTo` of the
witness): it may call it, and declares it or one of its indirect calls matches `h`'s signature,
with as many results. -/
def indToB (g h : Clif.Function) : Bool :=
  mayB g h.name && (declB g h.name || (indSigs g).any fun s =>
    decide (LinkSys.IndSigMatch s h) && h.sig.returns.length == s.returns.length)

/-- The scope of the indirect calls of `g` (`indSig`: the functions `g` may reach whose signature
one of its indirect calls matches, or that it declares and one of its indirect calls has the
parameter types of). -/
def indB (g : Clif.Function) : Bool :=
  indFreeB g || ((indSigs g).all (fun s => !s.params.any (·.purpose == .sret)) &&
    P.funcs.all (fun h => !mayB g h.name ||
      !((indSigs g).any (fun s => decide (LinkSys.IndSigMatch s h)) ||
        (declB g h.name && (indSigs g).any (fun s => decide (LinkSys.IndTyMatch s h)))) ||
      (!h.sig.params.any (·.purpose == .sret) &&
      (match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false))))

/-- Distinct names have distinct addresses; the functions with an address have no slots. -/
def symB : Bool :=
  (Clif.Program.names P).all (fun a => (Clif.Program.names P).all fun b =>
    !(symsW a == symsW b && (symsW a).isSome) || a == b) &&
  P.funcs.all (fun h => (symsW h.name).isNone || h.slots.isEmpty)

/-- `g` is called in `P`: a function of `P` declares it, or it has an address (a pointer may
reach it). -/
def calleeB (g : Clif.Function) : Bool :=
  P.funcs.any (fun g' => g'.externs.any fun e => e.2.name == g.name) || (symsW g.name).isSome

/-- The link-time symbol addresses: every function at its base, the vtable `vt` after the code. -/
def symTab : List (String × BitVec 64) :=
  [("f", 0x70000), ("g", 0x20000), ("h", 0x10000), ("s", 0x30000), ("k", 0x40000),
    ("r", 0x50000), ("r__fvself", 0x60000), ("q", 0x80000), ("v", 0x90000), ("a2", 0xA0000),
    ("w", 0xB0000), ("t", 0xC0000), ("u", 0xD0000), ("m", 0xE0000), ("d", 0xF0000),
    ("e", 0xF4000), ("y", 0xF6000), ("z", 0xF7000), ("vt", BitVec.ofNat 64 vtAddr)]

def symOf (n : String) : BitVec 64 := (symTab.lookup n).getD 0

/-- The slots of `g` fit in its compiled slot region (`LinkSys.Ok.slotFits`). -/
def slotFitsB (g : Clif.Function) (a : Art) : Bool :=
  g.slots.all fun p => match (slotLayout g.slots).1.lookup p.1 with
    | some off => decide (a.af.slotBase + off + p.2.size ≤ a.af.frameSize)
    | none => false

theorem slotFitsB_sound {g : Clif.Function} {a : Art} (h : slotFitsB g a = true) :
    ∀ p ∈ g.slots, ∃ off, (slotLayout g.slots).1.lookup p.1 = some off ∧
      a.af.slotBase + off + p.2.size ≤ a.af.frameSize := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  revert this
  cases (slotLayout g.slots).1.lookup p.1 with
  | none => simp
  | some off => exact fun h' => ⟨off, rfl, of_decide_eq_true h'⟩

/-- The per-function checks. -/
def chks (g : Clif.Function) : List Bool :=
  let a := A g
  let fr := RAFrame.compute a.vcp a.rf
  [(pipe g (idx g) (baseOf g)).toBool, lowerCheck g a.vc, prepCheck a.vc a.vcp,
    (checkAlloc a.vcp a.rf).toBool, formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp,
    allInsts a.vc (retsB g),
    g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase),
    decide (regLocs g.sig).Nodup, (regLocs g.sig).all (·.isArgReg),
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)),
    !calleeB g || ((!g.slots.isEmpty || fr.size == a.af.frameSize) && slotFitsB g a),
    allInsts a.vcp (siteB (siteOk P g (indToB g) a.vcp)),
    g.externs.all (fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
    entryB g a.vcp, decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64), raCallB P A g a,
    decide (frameDrop a.af ≤ 64), !hasTls g, linkFreeB g, Compile.functionE g,
    g.externs.all (fun e => e.2.name != g.name), sigAbiOk g.sig,
    g.externs.all (fun e => sigAbiOk e.2.sig), indSigsOk g, indB g]

def chk (g : Clif.Function) : Bool := (chks g).all id

/-- The symbol table has nonzero, distinct addresses and an entry for every function of `P`. -/
def symTabB : Bool :=
  symTab.all (fun p => p.2 != 0 && symTab.all fun q => p.2 != q.2 || p.1 == q.1) &&
  P.funcs.all fun h => (symTab.lookup h.name).isSome

/-- All the executable checks. -/
def okB : Bool :=
  decide (P.funcs.map (·.name)).Nodup && (P.funcs.all chk && (imgB P A && raStarB P A 8)) && symB &&
    symTabB

theorem okB_true : okB = true := by native_decide

theorem okB_imgB : imgB P A = true := by
  have := okB_true
  simp only [okB, Bool.and_eq_true] at this
  exact this.1.1.2.2.1

/-! ## Soundness of the image check -/

theorem wordsAt_mem {base : BitVec 64} {w : BitVec 32} :
    ∀ {ws : List (BitVec 32)} {k j : Nat}, ws[j]? = some w →
      List.Mem (base + BitVec.ofNat 64 (4 * (k + j)), w) (wordsAt base k ws)
  | [], _, _, h => by simp at h
  | x :: ws, k, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact .head _
  | x :: ws, k, j + 1, h => by
    apply List.Mem.tail
    have := wordsAt_mem (base := base) (ws := ws) (k := k + 1) (j := j) (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem rmb_congr {t t' : Arm.ArmState} : ∀ (n : Nat) (x : BitVec 64),
    (∀ i < n, t.mem (x + BitVec.ofNat 64 i) = t'.mem (x + BitVec.ofNat 64 i)) →
    Arm.read_mem_bytes n x t = Arm.read_mem_bytes n x t'
  | 0, _, _ => rfl
  | n + 1, x, h => by
    have h0 : t.mem x = t'.mem x := by simpa using h 0 (by omega)
    have ih := rmb_congr (t := t) (t' := t') n (x + 1#64) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega] at this
    simp only [Arm.read_mem_bytes, Arm.read_mem, Arm.read_store, ih, h0]

theorem imgCode_of {P : Clif.Program} {A : Clif.Function → Art} (h : imgB P A = true)
    {g : Clif.Function} (hg : g ∈ P.funcs) (t : Arm.ArmState)
    (ht : ∀ a, Img P A a → t.mem a = memOf (progAll P A) a) (k : Nat) (w : BitVec 32)
    (hw : (A g).fb.words[k]? = some w) :
    Arm.read_mem_bytes 4 ((A g).base + BitVec.ofNat 64 (4 * k)) t = w := by
  have hk : k < (A g).fb.words.size := (Array.getElem?_eq_some_iff.1 hw).1
  have hc := List.all_eq_true.1 (List.all_eq_true.1 h g hg) k (List.mem_range.2 hk)
  simp only [beq_iff_eq] at hc
  rw [show (A g).fb.words[k]! = w by simp [Array.getElem!_eq_getD, hw]] at hc
  rw [← hc]
  refine rmb_congr 4 _ fun i hi => ?_
  have hm := wordsAt_mem (base := (A g).base) (k := 0) (j := k) (ws := (A g).fb.words.toList)
    (by simpa using hw)
  rw [Nat.zero_add] at hm
  refine ht _ ⟨g, hg, ⟨_, hm, ?_⟩⟩
  rw [BitVec.add_comm _ (BitVec.ofNat 64 i), BitVec.add_sub_cancel]
  simp only [BitVec.toNat_ofNat]
  omega

/-! ## The facts the checks give -/

/-- What `chk g` says of `g`. -/
structure Facts (g : Clif.Function) : Prop where
  pipe : pipe g (idx g) (baseOf g) = .ok (A g)
  lowerOk : lowerCheck g (A g).vc = true
  prepOk : prepCheck (A g).vc (A g).vcp = true
  check : checkAlloc (A g).vcp (A g).rf = .ok ()
  covered : FormsCovered ⟨(A g).fa.k, (A g).af.slotBase⟩ (A g).vcp
  rets : allInsts (A g).vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, (P.func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute (A g).vcp (A g).rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB g = true → (g.slots = [] →
    (RAFrame.compute (A g).vcp (A g).rf).size = (A g).af.frameSize) ∧ slotFitsB g (A g) = true
  sites : allInsts (A g).vcp (siteB (siteOk P g (indToB g) (A g).vcp)) = true
  externs : ∀ e ∈ g.externs.map (·.2), ∀ h, P.func? e.name = some h → e.sig = h.sig
  entry : entryB g (A g).vcp = true
  fits : (A g).base.toNat + 4 * (A g).fb.words.size ≤ 2 ^ 64
  ra : raCallB P A g (A g) = true
  depth : frameDrop (A g).af ≤ 64
  tls : hasTls g = false
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  extName : ∀ e ∈ g.externs.map (·.2), e.name ≠ g.name
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB g = true

theorem toBool_unit {ε : Type} {x : Except ε Unit} (h : x.toBool = true) : x = .ok () := by
  cases x <;> simp_all [Except.toBool]

theorem chk_sound {g : Clif.Function} (h : chk g = true) : Facts g := by
  have hall : ∀ b ∈ chks g, b = true := by
    simpa [chk, List.all_eq_true] using h
  simp only [chks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h19 h22 h24
  refine ⟨getOk_eq h1, h2, h3, toBool_unit h4, (formsCoveredB_iff _ _).1 h5, h7,
    fun e he hs => ?_, h9, h10, h11, fun hc => ?_, h13, fun e he => ?_, h15, h16, h17, h18, ?_,
    linkFreeB_sound h20, h21, fun e he => ?_, ⟨h23, h24⟩, h25, h26⟩
  · rcases h8 e he with h | h
    · simp [hs] at h
    · exact h
  · rcases h12 with h | ⟨h', hfit⟩
    · simp [hc] at h
    · refine ⟨fun hs => ?_, hfit⟩
      rcases h' with h | h
      · simp [hs] at h
      · exact h
  · intro h hf
    obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    have := h14 _ hm
    simp only [hf, decide_eq_true_eq] at this
    exact this
  · simpa using h19
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    simpa using h22 _ hm

theorem facts {g : Clif.Function} (hg : g ∈ P.funcs) : Facts g := by
  have := okB_true
  simp only [okB, Bool.and_eq_true, List.all_eq_true] at this
  exact chk_sound (this.1.1.2.1 g hg)

/-! ## The linked program -/

/-- The base environment's machine semantics: no extern outside `P` (`call` undefined), the
symbols at the functions' bases. -/
def Xb : ExtSem where
  call _ _ _ := none
  sym n _ := symOf n
  tp := 0
  tlsFlags _ s := Arm.read_pstate s

/-- The base hooks: a call outside `P` continues at the next instruction; TLS keeps the state. -/
def Hb : ArmHooks := ⟨fun _ s => Arm.w .PC (Arm.r .PC s + 4) s, fun _ _ s => s⟩

/-- **The linked program** `{f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y, z}` with the
addresses `F` outside the world. -/
def L (F : BitVec 64 → Prop) : LinkSys where
  P := P
  A := A
  base := Clif.Env.empty
  Xb := Xb
  Hb := Hb
  syms := symsW
  F := F
  Img := Img P A
  imgMem := memOf (progAll P A)
  raStar := 8
  D := 64

theorem names : fF.name = "f" ∧ fG.name = "g" ∧ fH.name = "h" ∧ fS.name = "s" ∧ fK.name = "k" ∧
    fR.name = "r" ∧ fRS.name = "r__fvself" ∧ fQ.name = "q" ∧ fV.name = "v" ∧ fA2.name = "a2" ∧
    fW.name = "w" ∧ fT.name = "t" ∧ fU.name = "u" ∧ fM.name = "m" ∧ fD.name = "d" ∧
    fE.name = "e" ∧ fY.name = "y" ∧ fZ.name = "z" := by
  native_decide

theorem mem_P {g : Clif.Function} :
    g ∈ P.funcs ↔ g = fF ∨ g = fG ∨ g = fH ∨ g = fS ∨ g = fK ∨ g = fR ∨ g = fRS ∨ g = fQ ∨
      g = fV ∨ g = fA2 ∨ g = fW ∨ g = fT ∨ g = fU ∨ g = fM ∨ g = fD ∨ g = fE ∨ g = fY ∨
      g = fZ := by
  simp [P]

theorem lookup_pair {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i e
      cases h
      have : a = x := by simpa using e
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_pair h)

theorem symTab_facts : (∀ p ∈ symTab, p.2 ≠ 0 ∧ ∀ q ∈ symTab, p.2 ≠ q.2 ∨ p.1 = q.1) ∧
    ∀ h ∈ P.funcs, (symTab.lookup h.name).isSome := by
  have := okB_true
  simp only [okB, Bool.and_eq_true] at this
  simpa [symTabB, List.all_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] using this.2

theorem symInj {h : Clif.Function} (hh : h ∈ P.funcs) (n : String)
    (hn : Xb.sym h.name 0 = Xb.sym n 0) : n = h.name := by
  obtain ⟨hdist, hall⟩ := symTab_facts
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hall h hh)
  have hxm := lookup_pair hx
  simp only [Xb, symOf, hx, Option.getD_some] at hn
  cases hy : symTab.lookup n with
  | none => rw [hy] at hn; exact absurd hn (hdist _ hxm).1
  | some y =>
    rw [hy, Option.getD_some] at hn
    exact (((hdist _ hxm).2 _ (lookup_pair hy)).resolve_left (fun e => e hn)).symm

theorem symsW_some {n : String} {b : Nat} (h : symsW n = some b) :
    (n = "q" ∧ b = 0x80000) ∨ (n = "m" ∧ b = 0xE0000) ∨ (n = "vt" ∧ b = vtAddr) ∨
      (n = "k" ∧ b = 0x40000) ∨ (n = "s" ∧ b = 0x30000) := by
  unfold symsW at h
  split at h
  · cases h; exact .inl ⟨by assumption, rfl⟩
  · split at h
    · cases h; exact .inr (.inl ⟨by assumption, rfl⟩)
    · split at h
      · cases h; exact .inr (.inr (.inl ⟨by assumption, rfl⟩))
      · split at h
        · cases h; exact .inr (.inr (.inr (.inl ⟨by assumption, rfl⟩)))
        · split at h
          · cases h; exact .inr (.inr (.inr (.inr ⟨by assumption, rfl⟩)))
          · cases h

/-- `MayCall` of the witness is decided by `mayB`. -/
theorem mayB_of {F : BitVec 64 → Prop} {g : Clif.Function} {n : String}
    (h : (L F).MayCall g n) : mayB g n = true := by
  rcases h with h | ⟨hnf, hs, -⟩
  · simp [mayB, declB_of h]
  · have hi : indFreeB g = false := by
      cases e : indFreeB g
      · rfl
      · exact absurd (indFreeB_sound e) hnf
    have hs' : (symsW n).isSome = true := by
      simpa [L, Option.isSome_iff_ne_none] using hs
    simp [mayB, hi, hs']

theorem indToB_of {F : BitVec 64 → Prop} {g h : Clif.Function} (hi : (L F).IndTo g h) :
    indToB g h = true := by
  obtain ⟨hmay, ⟨hd, -⟩ | ⟨sig, hs, hm, hl⟩⟩ := hi
  · simp [indToB, mayB_of hmay, declB_of hd]
  · simp only [indToB, mayB_of hmay, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact .inr ⟨sig, hs, hm, hl⟩

/-- What `indB` says of a function with indirect calls. -/
theorem indFacts {F : BitVec 64 → Prop} {g : Clif.Function} (hg : g ∈ P.funcs)
    (hnf : ¬ Clif.IndFree g) :
    (∀ sig ∈ indSigs g, sig.params.any (·.purpose == .sret) = false) ∧
    (∀ h ∈ P.funcs, (L F).MayCall g h.name → ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
      (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      h.sig.params.any (·.purpose == .sret) = false ∧
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) := by
  have h := (facts hg).ind
  simp only [indB, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact absurd (indFreeB_sound h) hnf
  refine ⟨fun sig hs => by simpa using h1 sig hs, fun h' hh hd hm => ?_⟩
  have h2' := h2 h' hh
  rw [mayB_of hd] at h2'
  have hany : ((indSigs g).any (fun s => decide (LinkSys.IndSigMatch s h')) ||
      (declB g h'.name && (indSigs g).any (fun s => decide (LinkSys.IndTyMatch s h')))) = true := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    rcases hm with ⟨sig, hs, hm⟩ | ⟨hdn, sig, hs, hm⟩
    · exact .inl ⟨sig, hs, hm⟩
    · exact .inr ⟨declB_of hdn, sig, hs, hm⟩
  rw [hany] at h2'
  revert h2'
  cases hs : h'.sig.params.any (·.purpose == .sret) <;>
    cases hb : sigParamBytes h'.sig <;> simp_all

/-- The TLSDESC flags of the base (the world's `pstate`) are the same in two worlds that agree
on the unmasked fields. -/
theorem xbTls (F : BitVec 64 → Prop) : XTls F Xb := by
  intro Z n w w' _ hsw
  have e : ∀ fl, Arm.r (.FLAG fl) w = Arm.r (.FLAG fl) w' := fun fl => hsw.1 _ (by simp [Masked])
  have h1 := e .N
  have h2 := e .Z
  have h3 := e .C
  have h4 := e .V
  simp only [Arm.r, Arm.read_base_flag] at h1 h2 h3 h4
  show Arm.read_pstate w = Arm.read_pstate w'
  apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption

/-- **`L.Ok`**: every premise of the linked program, for every `F` containing the code. -/
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (L F).Ok := by
  have hok := okB_true
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hnames, -, himg, hstar⟩, hsym⟩, -⟩ := hok
  simp only [symB, Bool.and_eq_true, List.all_eq_true] at hsym
  obtain ⟨hinj, haddr⟩ := hsym
  have site : ∀ g ∈ P.funcs, ∀ info h, (L F).ProgSite g info h →
      h ∈ P.funcs ∧ h ≠ g ∧ calleeB h = true ∧ ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    obtain ⟨n', h', hd', hf', hne, ⟨e, he, hen⟩, Lu, Ld, heq, h1, h2⟩ :=
      siteOk_sound (site_sound (facts hg).sites hs) hd
    rw [hd] at hd'; cases hd'
    have : h' = h := by simp only [L] at hf; rw [hf] at hf'; cases hf'; rfl
    subst this
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, hne, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inl ⟨g, hg, e, he, by rw [hen, hname]⟩
  have hcal : ∀ g ∈ P.funcs, ∀ h, (L F).Callee g h → (h.slots = [] →
      (RAFrame.compute (A h).vcp (A h).rf).size = (A h).af.frameSize) ∧
      slotFitsB h (A h) = true := by
    intro g hg h hh
    have hc : calleeB h = true ∧ h ∈ P.funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, he, hf⟩ | ⟨hh', hm⟩
      · obtain ⟨hh', -, hc, -⟩ := site g hg info h hs
        exact ⟨hc, hh'⟩
      · obtain ⟨hh', hname⟩ := Clif.Program.func?_some hf
        refine ⟨?_, hh'⟩
        obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        exact .inl ⟨g, hg, (fn, e'), hm, hname.symm⟩
      · refine ⟨?_, hh'⟩
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        rcases hm with ⟨hd, -⟩ | ⟨-, hs, -⟩
        · obtain ⟨⟨fn, e'⟩, hm, hen⟩ := List.mem_map.1 hd
          exact .inl ⟨g, hg, (fn, e'), hm, hen⟩
        · exact .inr (by simpa [L, Option.isSome_iff_ne_none] using hs)
    exact (facts hc.2).callee hc.1
  refine
    { names := hnames
      free := fun g hg => (facts hg).free
      subset := fun g hg => ⟨(facts hg).subsetE, ?_, ?_, (facts hg).abi, ?_⟩
      compiled := fun g hg => ?_
      covered := fun g hg => (facts hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := fun _ n gsem hn => by simp [L, Clif.Env.empty] at hn
      argRegs := fun g hg => ⟨(facts hg).nodup, (facts hg).argReg, (facts hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (facts hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2.2
      blrRegs := fun g hg info hs hreg => by
        obtain ⟨t, Lu, Ld, hi, hall⟩ := blrOk_sound (siteOk_reg (site_sound (facts hg).sites hs) hreg)
        exact ⟨t, Lu, Ld, hi, fun h hh hb =>
          hall h hh (indToB_of hb.1) fun n hn => (hb.2 n (gotOf_sound hn)).symm⟩
      raBlr := fun g hg info hs hreg h hh hdecl pc hpc => by
        by_cases hhg : h = g
        · subst hhg
          exact .inr ⟨hpc, (raCallB_parts (facts hh).ra hpc).1⟩
        · exact raCallB_sound (facts hg).ra hpc h hh hhg
      indScope := fun g hg hnf => ⟨fun n f h => by simp [L, Clif.Env.empty] at h,
        fun a ha b hb x hxa hxb => by
          obtain ⟨ga, hga, rfl⟩ := List.mem_map.1 ha
          obtain ⟨gb, hgb, rfl⟩ := List.mem_map.1 hb
          have := hinj _ (Clif.names_func hga) _ (Clif.names_func hgb)
          simp only [L] at hxa hxb
          rw [hxa, hxb] at this
          simpa using this,
        fun _ _ _ _ _ _ _ _ _ => by simp [L, Clif.Env.empty]⟩
      indSig := fun g hg hnf h hh hmay hm => by
        obtain ⟨hns, hb⟩ := (indFacts (F := F) hg hnf).2 h hh hmay hm
        refine ⟨hb, fun sig hs _ hl => ?_⟩
        rw [sigRets_of_noSret hns, sigRets_of_noSret ((indFacts (F := F) hg hnf).1 sig hs), hl]
      addrSlots := fun _ _ _ h hh hs => by
        have := haddr h hh
        simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at this
        exact this.resolve_left hs
      symInj := fun h hh n hn => symInj hh n hn
      declSig := fun g hg e he h hf => ?_
      entryRegs := fun g hg r hr => entryB_sound (facts hg).entry hr
      fits := fun g hg => (facts hg).fits
      imgAddr := fun g hg a ha => ⟨g, hg, ha⟩
      imgCode := fun g hg t ht k w hw => imgCode_of himg hg t ht k w hw
      imgF := hF
      raCall := fun g hg info h hs pc hpc => ?_
      raStar := fun h hh k hk => ?_
      depth := fun g hg => (facts hg).depth
      symOk := fun n b hn => by
        rcases symsW_some hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · show symOf "q" = _; decide
        · show symOf "m" = _; decide
        · show symOf "vt" = _; decide
        · show symOf "k" = _; decide
        · show symOf "s" = _; decide
      baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
        _ hsem => by simp [csem, L, Xb] at hsem
      basePc := fun d s _ _ _ => by simp [L, Hb, Arm.r_of_w_same]
      baseExt := fun d uses w outs w' _ hx => by simp [L, Xb] at hx
      baseX := fun g hg F' slotOff out c ext _ gsem sl cm w d uses args vals rvals cm' hgs => by
        simp [L, Clif.Env.empty] at hgs
      baseXI := fun g hg F' slotOff out c sig _ n gsem sl cm w u args vals rvals cm' hgs => by
        simp [L, Clif.Env.empty] at hgs
      baseTls := fun g hg ht => absurd ht (by simp [L, (facts hg).tls])
      baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
        simp [csem, L, Xb] at hsem
      baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
        simp [L, Xb] at hx
      baseTlsNI := fun _ F' => xbTls F'
      baseKeepsPlace := fun _ n gsem hn => by simp [L, Clif.Env.empty] at hn
      baseKeepsAllocs := fun _ n gsem hn => by simp [L, Clif.Env.empty] at hn }
  · intro b _ st _ fn args _ e he
    have hne := (facts hg).extName e (lookup_mem he)
    simp [L, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · intro b _ fn args et _ e he
    have hne := (facts hg).extName e (lookup_mem he)
    simp [L, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · intro sig hs
    have := List.all_eq_true.mp (facts hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  · obtain ⟨hl, hp, ha, he, hla, -, -⟩ := pipe_spec (facts hg).pipe
    exact ⟨hl, (facts hg).lowerOk, hp, (facts hg).prepOk, (facts hg).check, ha, he, hla⟩
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    exact outFitsB_sound ((facts hg).outFits _ hm hs) hl hp
  · simp only [L] at hf
    exact (facts hg).externs e he h hf
  · obtain ⟨hh, hne, -⟩ := site g hg info h hs
    exact raCallB_sound (facts hg).ra hpc h hh hne
  · simp only [raStarB, List.all_eq_true, List.mem_range, bne_iff_ne] at hstar
    exact hstar h hh k hk

/-! ## A concrete entry of `f` -/

/-- The call depth of the witness run. -/
def M0 : Nat := 100

def sp0 : BitVec 64 := 0x100000

/-- The argument `41 : i64`. -/
def arg : Clif.Val := ⟨.i64, 41#64⟩

/-- The entry block of `f`. -/
def bF : Clif.Block := fF.entry?.getD default

/-- The address of `f`'s stack slot `ss0` in its frame: the body's `sp` (`sp0 - 64`) plus the
slot base `32`. -/
def slotAddr : Nat := 0x100000 - 32

/-- The slot-placement oracle's frames of the linked program (`LinkSys.frames`): every function
of `P` at its compiled frame. -/
def framesW (n : String) : Option (Nat × (Clif.SlotId → Nat)) :=
  (P.func? n).map fun h => (frameDrop (A h).af,
    fun id => (A h).af.slotBase + ((slotLayout h.slots).1.lookup id).getD 0)

theorem frames_eq (F : BitVec 64 → Prop) : (L F).frames = framesW := rfl

/-- **The vtable of `m`** as `cg_clif` emits a trait object's: a read-only data object whose
first word is the drop entry (null) and whose second word is the address of the method `m`
(an `Abs8` relocation, resolved through the link-time symbols). -/
def vtObj : Clif.DataObject :=
  { name := "vt", align := 8, items := List.replicate 8 (.byte 0) ++ [.addr "m" 0] }

/-- The entry memory before the vtable's contents: `f`'s slot (uninitialised) and the vtable's
read-only allocation, the link-time symbols, the slot-placement oracle at `f`'s body `sp`
(`sp0 - 64`) with the program's frames. -/
def mem0 : Clif.Mem :=
  { allocs := [{ base := slotAddr, size := 8 }, { base := vtAddr, size := 16, readonly := true }],
    symbols := symsW, place := some ⟨[sp0 - 64], framesW⟩ }

/-- The vtable written at `vt` by the image loader (`Clif.Image.writeItems`: the relocation
resolved through the link-time symbol of `m`). -/
def vtWrite : Clif.Res Clif.Mem := Clif.Image.writeItems [("m", 0xE0000)] mem0 vtAddr vtObj.items

/-- The entry memory: `mem0` with the bytes the loader wrote. -/
def memV : Clif.Mem :=
  { mem0 with bytes := match vtWrite with
    | .ok m => m.bytes
    | _ => mem0.bytes }

def vtWriteOk : Bool := match vtWrite with
  | .ok _ => true
  | _ => false

/-- The CLIF entry state of `f` on `41`: its slot at its frame address, the vtable in memory,
the slot-placement oracle at `f`'s body `sp` with the program's frames. -/
def cs0 : Clif.State where
  frame := { func := fF, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).getD default,
             slots := [(0, slotAddr)], body := bF.body, term := bF.term }
  callers := []
  mem := memV

/-- The CLIF run of the program from `cs0`. -/
def run0 : Clif.Outcome := Clif.runLoop Clif.Env.empty P (M0 + 1) cs0

def retVals : Clif.Outcome → List Clif.Val
  | .returned v _ => v
  | _ => []

def retMem : Clif.Outcome → Clif.Mem
  | .returned _ m => m
  | _ => Clif.Mem.empty

def isRet : Clif.Outcome → Bool
  | .returned _ _ => true
  | _ => false

theorem eq_returned {o : Clif.Outcome} (h : isRet o = true) : o = .returned (retVals o) (retMem o) := by
  cases o <;> simp_all [isRet, retVals, retMem]

/-- Every code address of `P` is in `[0x10000, 0xF8000)`. -/
def boundB : Bool :=
  P.funcs.all fun g => let a := A g
    decide (a.base.toNat + 4 * a.fb.words.size + 4 ≤ 0xF8000)

def locB : Bool :=
  match locsOf fF.sig with
  | [.reg (.x 0)] => true
  | _ => false

/-- The frame of `f`: 64 bytes below the entry `sp` (fp/lr, a 48-byte frame: the 16-byte
outgoing area, 16 bytes of saves, the 8-byte slot at `32`). -/
def frameB : Bool :=
  (A fF).af.frame && decide (frameDrop (A fF).af = 64) && decide ((A fF).af.frameSize = 48) &&
  decide ((A fF).af.slotBase = 32) && decide ((RAFrame.compute (A fF).vcp (A fF).rf).intBase = 16) &&
  decide ((RAFrame.compute (A fF).vcp (A fF).rf).size = 32) &&
  decide ((slotLayout fF.slots).1 = [(0, 0)]) && decide (fF.slots.map (·.1) = [0])

/-- The entry facts of `f` and its run: `f 41 = d (vt, u (t (w (v (g (k (s 41, 0, …, 41)) +
r 3)))))` returns `802`; the loader wrote the vtable, and `f`'s slot is uninitialised. -/
def entryFactsB : Bool :=
  boundB && locB && frameB &&
  decide (P.func? fF.name = some fF) && decide (fF.entry? = some bF) &&
  decide ([arg].map (·.ty) = fF.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = [arg].map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).isSome &&
  isRet run0 && decide (retVals run0 = [⟨.i64, 802#64⟩]) && vtWriteOk &&
  (List.range 8).all (fun i => memV.bytes (slotAddr + i) == none)

theorem entryFactsB_true : entryFactsB = true := by native_decide

theorem entryFacts :
    boundB = true ∧ locB = true ∧ frameB = true ∧ P.func? fF.name = some fF ∧
    fF.entry? = some bF ∧ [arg].map (·.ty) = fF.sig.params.map (·.ty) ∧
    bF.params.map (·.2) = [arg].map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).isSome = true ∧ isRet run0 = true ∧
    retVals run0 = [⟨.i64, 802#64⟩] ∧ vtWriteOk = true ∧
    ∀ i < 8, memV.bytes (slotAddr + i) = none := by
  have he := entryFactsB_true
  simp only [entryFactsB, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := he
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun i hi => ?_⟩
  have := List.all_eq_true.mp h12 i (List.mem_range.mpr hi)
  simpa using this

theorem frameFacts :
    (A fF).af.frame = true ∧ frameDrop (A fF).af = 64 ∧ (A fF).af.frameSize = 48 ∧
    (A fF).af.slotBase = 32 ∧ (RAFrame.compute (A fF).vcp (A fF).rf).intBase = 16 ∧
    (RAFrame.compute (A fF).vcp (A fF).rf).size = 32 ∧ (slotLayout fF.slots).1 = [(0, 0)] ∧
    fF.slots.map (·.1) = [0] := by
  have h := entryFacts.2.2.1
  simp only [frameB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem wordsAt_mem_inv {base : BitVec 64} {p : BitVec 64 × BitVec 32} :
    ∀ {ws : List (BitVec 32)} {k : Nat}, List.Mem p (wordsAt base k ws) →
      ∃ j < ws.length, p.1 = base + BitVec.ofNat 64 (4 * (k + j))
  | [], _, h => nomatch h
  | x :: ws, k, h => by
    cases h with
    | head => exact ⟨0, by simp, by simp⟩
    | tail _ h =>
      obtain ⟨j, hj, e⟩ := wordsAt_mem_inv h
      exact ⟨j + 1, by simp; omega, by rw [e]; congr 2; omega⟩

theorem codeAddr_lt {a : Art} (hb : a.base.toNat + 4 * a.fb.words.size + 4 ≤ 0xF8000) {x : BitVec 64}
    {t : Arm.ArmState} (ht : t.program = a.fb.program a.base) (h : CodeAddr t x) :
    x.toNat < 0xF8000 := by
  obtain ⟨p, hp, hx⟩ := h
  rw [ht] at hp
  obtain ⟨j, hj, e⟩ := wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := a.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

theorem bound_of {g : Clif.Function} (hg : g ∈ P.funcs) :
    (A g).base.toNat + 4 * (A g).fb.words.size + 4 ≤ 0xF8000 := by
  have h := entryFacts.1
  simp only [boundB, List.all_eq_true, decide_eq_true_eq] at h
  exact h g hg

theorem img_lt {x : BitVec 64} (h : Img P A x) : x.toNat < 0xF8000 := by
  obtain ⟨g, hg, hc⟩ := h
  exact codeAddr_lt (bound_of hg) rfl hc

/-- The Arm memory of the entry: the vtable's bytes at `vt` (as the loader wrote them), the code
image elsewhere. -/
def memS : Arm.Memory := fun a =>
  if vtAddr ≤ a.toNat ∧ a.toNat < vtAddr + 16 then (memV.bytes a.toNat).getD 0
  else memOf (progAll P A) a

/-- The ABI entry state of `f`: its code loaded at its base (program and memory, the image of
the whole program in memory, and the vtable), the argument `41` in x0, `sp = 0x100000`, return
address `8`. -/
def s0 : Arm.ArmState :=
  Arm.w .PC (A fF).base (Arm.w (.GPR 30#5) 8 (Arm.w (.GPR 31#5) sp0 (Arm.w (.GPR 0#5) 41#64
    (setMem (Arm.set_program Arm.ArmState.default ((A fF).fb.program (A fF).base)) memS))))

/-- The body-entry world: after the prologue (`stp x29, x30, [sp, #-16]!; mov x29, sp;
sub sp, sp, #48`). -/
def w0 : Arm.ArmState := Arm.w (.GPR 31#5) (sp0 - 64) (Arm.w (.GPR 29#5) (sp0 - 16) s0)

/-- The addresses outside the world of the entry activation: its frame, its callees' stack,
the code. -/
def F0 : BitVec 64 → Prop :=
  frameWG (64 * M0) (RAFrame.compute (A fF).vcp (A fF).rf).intBase
    (RAFrame.compute (A fF).vcp (A fF).rf).size (A fF).af (Img P A) s0

theorem mem_w (f : Arm.StateField) (v : Arm.state_value f) (s : Arm.ArmState) :
    (Arm.w f v s).mem = s.mem :=
  funext fun a => (Arm.read_mem_of_w (addr := a) (fld := f) (v := v) (s := s) :)

theorem s0_mem : s0.mem = memS := by simp [s0, mem_w]

theorem s0_img {a : BitVec 64} (h : Img P A a) : s0.mem a = memOf (progAll P A) a := by
  have := img_lt h
  rw [s0_mem]
  unfold memS
  rw [if_neg (by unfold vtAddr; omega)]

theorem s0_program : s0.program = (A fF).fb.program (A fF).base := by
  simp [s0, Arm.w_program]

theorem spv_s0 : spv s0 = sp0 := by simp [s0, spv, Arm.r_of_w_different, Arm.r_of_w_same]

theorem spv_w0 : spv w0 = sp0 - 64 := by simp [w0, spv, Arm.r_of_w_same]

/-- The frame of `f` above its body `sp`, outside the spill/save area `[16, 32)` and fp/lr
`[48, 64)`, and the outgoing area `[0, 16)` belong to the world. -/
theorem not_F0 {x : BitVec 64} (h1 : 0xFFFC0 ≤ x.toNat) (h2 : x.toNat < 0x100000)
    (h3 : ¬ (0xFFFD0 ≤ x.toNat ∧ x.toNat < 0xFFFE0)) (h4 : x.toNat < 0xFFFF0) : ¬ F0 x := by
  obtain ⟨hfr, hd, hfs, -, hib, hsz, -⟩ := frameFacts
  have hbody : (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af)).toNat = 0xFFFC0 := by
    rw [spv_s0, hd]; decide
  have hsub : (x - (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af))).toNat = x.toNat - 0xFFFC0 := by
    rw [spv_s0, hd]
    simp only [sp0]
    bv_omega
  simp only [F0, frameWG, frameW, frameF, StackBelow, hib, hsz, hsub, hbody, hfs]
  rintro (((⟨ha, hb⟩ | ⟨ha, hb⟩ | hc) | ⟨hlt, -⟩) | hi)
  · omega
  · rw [hd] at hb; omega
  · have := codeAddr_lt (bound_of (g := fF) (by simp [P])) s0_program hc; omega
  · omega
  · have := img_lt hi; omega

/-- The vtable is in the world of the entry activation (below the callees' stack, above the
code). -/
theorem not_F0_vt {x : BitVec 64} (h1 : vtAddr ≤ x.toNat) (h2 : x.toNat < vtAddr + 16) :
    ¬ F0 x := by
  obtain ⟨hfr, hd, hfs, -, hib, hsz, -⟩ := frameFacts
  simp only [vtAddr] at h1 h2
  have hbody : (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af)).toNat = 0xFFFC0 := by
    rw [spv_s0, hd]; decide
  have hsub : (x - (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af))).toNat =
      x.toNat + 2 ^ 64 - 0xFFFC0 := by
    rw [spv_s0, hd]
    simp only [sp0]
    bv_omega
  simp only [F0, frameWG, frameW, frameF, StackBelow, hib, hsz, hsub, hbody, hfs, M0]
  rintro (((⟨ha, hb⟩ | ⟨ha, hb⟩ | hc) | ⟨hlt, hle⟩) | hi)
  · omega
  · rw [hd] at hb; omega
  · have := codeAddr_lt (bound_of (g := fF) (by simp [P])) s0_program hc; omega
  · omega
  · have := img_lt hi; omega

theorem gpr_ne {i j : Nat} (hi : i < 32) (hj : j < 32) (h : i ≠ j) :
    Arm.StateField.GPR (BitVec.ofNat 5 i) ≠ .GPR (BitVec.ofNat 5 j) := by
  intro e
  injection e with e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- `vc` has a `call` of the symbol `n`. -/
def callsB (vc : VCode) (n : String) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .call info => decide (info.dest = .sym n)
    | _ => false

theorem callsB_sound {vc : VCode} {n : String} (h : callsB vc n = true) :
    ∃ info, vc.CallSite info ∧ info.dest = .sym n := by
  simp only [callsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i info e
    intro hd
    exact ⟨info, ⟨b, _, k, Array.getElem?_eq_getElem hb, .inl (by rw [Array.getElem?_eq_getElem hk, e])⟩,
      of_decide_eq_true hd⟩
  · simp

/-- `vc` has a `try_call` of the symbol `n`. -/
def tryCallsB (vc : VCode) (n : String) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .tryCall info _ => decide (info.dest = .sym n)
    | _ => false

theorem tryCallsB_sound {vc : VCode} {n : String} (h : tryCallsB vc n = true) :
    ∃ info ti, vc.TrySite info ti ∧ info.dest = .sym n := by
  simp only [tryCallsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i info ti e
    intro hd
    exact ⟨info, ti, ⟨b, _, k, Array.getElem?_eq_getElem hb, by rw [Array.getElem?_eq_getElem hk, e]⟩,
      of_decide_eq_true hd⟩
  · simp

/-- `vc` has a `call` through a register (`blr`). -/
def regCallsB (vc : VCode) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .call info => (match info.dest with | .reg _ => true | .sym _ => false)
    | _ => false

theorem regCallsB_sound {vc : VCode} (h : regCallsB vc = true) :
    ∃ info, vc.CallSite info ∧ ∀ n, info.dest ≠ .sym n := by
  simp only [regCallsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i info e
    intro hd
    refine ⟨info, ⟨b, _, k, Array.getElem?_eq_getElem hb, .inl (by rw [Array.getElem?_eq_getElem hk, e])⟩,
      fun n hn => ?_⟩
    rw [hn] at hd; cases hd
  · simp

/-- `f` calls `s` (an `sret` callee), `k` (a stack-passed argument), `g` by a `try_call` and
the recursive `r`; `g` calls `h`; `r` and its alias `r__fvself` call each other (in their
compiled code). -/
def callChainB : Bool :=
  tryCallsB (A fF).vcp "g" && callsB (A fG).vcp "h" && callsB (A fF).vcp "s" &&
  callsB (A fF).vcp "k" &&
  decide (P.func? "g" = some fG) && decide (P.func? "h" = some fH) &&
  decide (P.func? "s" = some fS) && decide (P.func? "k" = some fK) &&
  fS.sig.params.any (·.purpose == .sret) &&
  (locsOf fK.sig).any (fun l => match l with | .stack _ => true | .reg _ => false) &&
  callsB (A fR).vcp "r__fvself" && callsB (A fRS).vcp "r" && callsB (A fF).vcp "r" &&
  decide (P.func? "r" = some fR) && decide (P.func? "r__fvself" = some fRS) &&
  decide (fRS.name = fR.name ++ "__fvself") && decide (fRS.blocks = fR.blocks) &&
  decide (fRS.sig = fR.sig) &&
  callsB (A fF).vcp "v" && decide (P.func? "v" = some fV) && decide (P.func? "q" = some fQ) &&
  regCallsB (A fV).vcp && !indFreeB fV && declB fV "q" && decide (symsW "q" = some 0x80000) &&
  callsB (A fF).vcp "w" && callsB (A fW).vcp "a2" && decide (P.func? "w" = some fW) &&
  decide (P.func? "a2" = some fA2) &&
  (Opt.Legalize128.function128Cert (srcFn 9)).toBool &&
  decide ((getOk (Opt.Legalize128.function128Cert (srcFn 9))).1 = fA2) &&
  Opt.Legal.check (srcFn 9) fA2 (certOf 9) &&
  (Opt.Legalize128.function128Cert (srcFn 10)).toBool &&
  decide ((getOk (Opt.Legalize128.function128Cert (srcFn 10))).1 = fW) &&
  Opt.Legal.check (srcFn 10) fW (certOf 10) &&
  decide ((srcFn 9).sig.params.map (·.ty) = [.i128, .i128]) &&
  decide ((srcFn 9).sig.returns.map (·.ty) = [.i128]) &&
  decide (fA2.sig.params.map (·.ty) = [.i64, .i64, .i64, .i64]) &&
  decide (fA2.sig.returns.map (·.ty) = [.i64, .i64])

theorem callChainB_true : callChainB = true := by native_decide

/-- A call of `a`'s code (laid out at its base) returns into `b`'s code. -/
def retIntoB (a b : Art) : Bool :=
  let ls := a.fa.lines.toList
  (List.range ls.length).any fun j => match ls[j]? with
    | some l => callLine l && (List.range b.fb.words.size).any fun k =>
        a.base + BitVec.ofNat 64 (lineOffset ls j) + 4 == b.base + BitVec.ofNat 64 (4 * k)
    | none => false

theorem retIntoB_sound {a b : Art} (h : retIntoB a b = true) :
    ∃ pc, CallPc a.fa a.base pc ∧ ∃ k < b.fb.words.size, pc + 4 = b.base + BitVec.ofNat 64 (4 * k) := by
  simp only [retIntoB, List.any_eq_true, List.mem_range] at h
  obtain ⟨j, -, hl⟩ := h
  revert hl
  cases e : a.fa.lines.toList[j]? with
  | none => simp
  | some l =>
    intro hl
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at hl
    obtain ⟨hc, k, hk, he⟩ := hl
    refine ⟨_, ?_, k, hk, he⟩
    cases l with
    | ins i t =>
      cases i <;> simp only [callLine, Bool.false_eq_true] at hc
      · exact ⟨j, _, t, e, .inl ⟨_, rfl⟩, rfl⟩
      · exact ⟨j, _, t, e, .inr ⟨_, rfl⟩, rfl⟩
    | _ => simp [callLine] at hc

/-- `r` and its alias `r__fvself` are one copy of code (the same load address and words), and the
calls of each return into the other's code. -/
def oneCopyB : Bool :=
  decide ((A fRS).base = (A fR).base) && decide ((A fRS).fb.words = (A fR).fb.words) &&
  retIntoB (A fR) (A fRS) && retIntoB (A fRS) (A fR)

theorem oneCopyB_true : oneCopyB = true := by native_decide

/-- `k` (a stack-passed parameter: more than 8 argument registers' worth) has an address, but the
indirect caller `v` does not declare it and no indirect call of `v` has `k`'s parameter types, so
`v` cannot reach it. -/
def sigChainB : Bool :=
  decide (symsW "k" = some 0x40000) && !declB fV "k" &&
  (indSigs fV).all (fun s => !decide (Clif.AbiParam.tys fK.sig.params = Clif.AbiParam.tys s.params)) &&
  (match sigParamBytes fK.sig with | .ok b => decide (8 < b.length) | .error _ => true)

theorem sigChainB_true : sigChainB = true := by native_decide

/-- `f` calls `t` (a callee with a stack slot, beyond its allocator frame: a slot region) and `u`
(a callee with an outgoing-argument area: it passes a stack argument to `k`). -/
def slotChainB : Bool :=
  callsB (A fF).vcp "t" && callsB (A fF).vcp "u" && callsB (A fU).vcp "k" &&
  decide (P.func? "t" = some fT) && decide (P.func? "u" = some fU) &&
  !fT.slots.isEmpty && decide ((RAFrame.compute (A fU).vcp (A fU).rf).intBase ≠ 0) &&
  decide ((RAFrame.compute (A fT).vcp (A fT).rf).size ≠ (A fT).af.frameSize)

theorem slotChainB_true : slotChainB = true := by native_decide

/-- `f` calls the dispatcher `d` with the vtable's address; `d` declares nothing and calls
through a register (`call_indirect` of the method loaded from the vtable); the vtable's second
word is a relocation to `m`, which has an address. -/
def vtChainB : Bool :=
  callsB (A fF).vcp "d" && decide (P.func? "d" = some fD) && decide (P.func? "m" = some fM) &&
  regCallsB (A fD).vcp && !indFreeB fD && fD.externs.isEmpty &&
  decide (symsW "m" = some 0xE0000) && decide (symsW "vt" = some vtAddr) &&
  decide (vtObj.items.drop 8 = [.addr "m" 0])

theorem vtChainB_true : vtChainB = true := by native_decide

/-- A call of `vc` through the GOT entry of `n` (`gotOf`) whose register arguments are as many as
the registers `rl` but not those registers. -/
def gotCallB (vc : VCode) (n : String) (rl : List Reg) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .call ⟨.reg (.vreg t .int), us, ds⟩ =>
      decide (us = retPairs (decU us)) && decide (ds = callDefs (decD ds)) &&
        decide (gotOf vc t = some n) && decide (rl.length = (decU us).length) &&
        decide ((decU us).map (·.2) ≠ rl)
    | _ => false

theorem gotCallB_sound {vc : VCode} {n : String} {rl : List Reg} (h : gotCallB vc n rl = true) :
    ∃ info t Lu Ld, vc.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      GotV vc t n ∧ rl.length = Lu.length ∧ Lu.map (·.2) ≠ rl := by
  simp only [gotCallB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i t us ds e
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨⟨⟨⟨hu, hd⟩, hg⟩, hl⟩, hne⟩
    refine ⟨_, t, decU us, decD ds,
      ⟨b, _, k, Array.getElem?_eq_getElem hb, .inl (by rw [Array.getElem?_eq_getElem hk, e])⟩,
      by rw [← hu, ← hd], gotOf_sound hg, hl, hne⟩
  · simp

/-- `e` declares the program function `s` (`sret`: arguments in x8, x0; one ABI result) and calls
the base extern `pz` (not in `P`) through the GOT with two register arguments in other registers
than `s`'s. -/
def gotChainB : Bool :=
  decide (P.func? "e" = some fE) && decide (P.func? "pz" = none) && declB fE "s" && indFreeB fE &&
  gotCallB (A fE).vcp "pz" (regLocs fS.sig) && decide ((sigRets fS.sig).length = 1)

theorem gotChainB_true : gotChainB = true := by native_decide

/-- A `blr` call of `vc` whose register arguments are as many as the registers `rl` but not those
registers. -/
def blrArgsB (vc : VCode) (rl : List Reg) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .call ⟨.reg (.vreg _ .int), us, ds⟩ =>
      decide (us = retPairs (decU us)) && decide (ds = callDefs (decD ds)) &&
        decide (rl.length = (decU us).length) && decide ((decU us).map (·.2) ≠ rl)
    | _ => false

theorem blrArgsB_sound {vc : VCode} {rl : List Reg} (h : blrArgsB vc rl = true) :
    ∃ info t Lu Ld, vc.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      rl.length = Lu.length ∧ Lu.map (·.2) ≠ rl := by
  simp only [blrArgsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i t us ds e
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨⟨⟨hu, hd⟩, hl⟩, hne⟩
    refine ⟨_, t, decU us, decD ds,
      ⟨b, _, k, Array.getElem?_eq_getElem hb, .inl (by rw [Array.getElem?_eq_getElem hk, e])⟩,
      by rw [← hu, ← hd], hl, hne⟩
  · simp

/-- `y` has indirect calls and declares nothing; `s` has an address; `y` has a `blr` site with as
many register arguments as `s` has register parameters, in other registers (`s`'s `sret` pointer
is in x8), but no indirect call of `y` matches `s`'s signature. -/
def blrChainB : Bool :=
  decide (P.func? "y" = some fY) && !indFreeB fY && decide (fY.externs = []) &&
  decide (symsW "s" = some 0x30000) &&
  (indSigs fY).all (fun s => !decide (LinkSys.IndSigMatch s fS)) &&
  blrArgsB (A fY).vcp (regLocs fS.sig)

theorem blrChainB_true : blrChainB = true := by native_decide

/-- `z` has indirect calls and declares nothing; `s` has an address and an `sret` parameter; an
indirect call of `z` has `s`'s parameter types and number of results, but none matches `s`'s
signature (the parameter purposes differ); `z` has a `blr` site with as many register arguments
as `s` has register parameters, in other registers. -/
def zChainB : Bool :=
  decide (P.func? "z" = some fZ) && !indFreeB fZ && decide (fZ.externs = []) &&
  decide (symsW "s" = some 0x30000) && fS.sig.params.any (·.purpose == .sret) &&
  (indSigs fZ).any (fun s =>
    decide (LinkSys.IndTyMatch s fS) && decide (s.returns.length = fS.sig.returns.length)) &&
  (indSigs fZ).all (fun s => !decide (LinkSys.IndSigMatch s fS)) &&
  blrArgsB (A fZ).vcp (regLocs fS.sig)

theorem zChainB_true : zChainB = true := by native_decide

/-- **Non-vacuity of `backend_correct_program`**: for the program
`P = {f, g, h, s, k, r, r__fvself, q, v, a2, w, t, u, m, d, e, y, z}` — `f` passes an `sret` pointer to
its stack slot to `s`, a stack-passed argument to `k`, calls `g` by a `try_call` with a result,
the recursive `r`, `v`, `t` (a callee with a stack slot), `u` (a callee passing a stack argument
to `k`) and `d` with the address of the vtable `vt`; `g` calls `h` (a non-leaf callee); `r`
recurses through its alias `r__fvself` (same body and signature, one copy of the code: the same
address and words, so each call returns into the callee's own code); `v` calls `q` through a pointer
(`call_indirect` of `func_addr`) and through the GOT, and cannot reach `k` (which has an address and
a stack-passed parameter): no indirect call of `v` has `k`'s parameter types (`indSig` constrains
only the reachable callees); `w` passes `i128` pairs to `a2` (both
legalised by `Opt.Legalize128`); `d` calls the method `m` it loads from the vtable (a read-only
data object holding `m`'s address, written by the loader) without declaring it; `e` calls the
base extern `pz` through the GOT next to the declared `s` of the same arity, whose argument
registers differ; `y` calls a pointer with two register arguments next to `s` (which has an address
and other argument registers) but with no indirect call matching `s`'s signature (`blrRegs`
constrains only the functions a `blr` can enter, `IndTo`); `z` calls a pointer with the signature
`(i64, i64)`, which has the parameter types of `s` (`(i64 sret, i64)`) but not its parameter
purposes, so `z` cannot reach `s` (`Clif.stepCallIndirect` requires the purposes to match, and
`MayCall` follows it): `indSig` (which `s`'s `sret` pointer would fail) and `blrRegs` (x8/x0
against the call's x0/x1) do not constrain `s` there —, compiled by
the backend's pipeline (regalloc2's allocation, accepted by `checkAlloc`), every premise of the
theorem holds — `L.Ok` (with `NeedSlots` and `NeedNI`: its non-interference and placement
premises are discharged, not vacuous) and the entry premises of `f` on the argument `41`
(including the slot-placement oracle at `f`'s body `sp`) — and the theorem gives: the linked Arm
machine refines `f`'s CLIF run, which returns `802`. -/
theorem backend_correct_program_witness :
    (L F0).Ok ∧ fF ∈ (L F0).P.funcs ∧ fG ∈ (L F0).P.funcs ∧ fH ∈ (L F0).P.funcs ∧
    fQ ∈ (L F0).P.funcs ∧ fV ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fV) ∧
    ¬ Clif.IndFree fV ∧ (∃ info, (A fV).vcp.CallSite info ∧ ∀ n, info.dest ≠ .sym n) ∧
    DeclN fV fQ.name ∧ (L F0).syms fQ.name = some 0x80000 ∧
    (L F0).syms fK.name = some 0x40000 ∧ ¬ (L F0).MayCall fV fK.name ∧
    (∀ sig ∈ indSigs fV, ¬ LinkSys.IndTyMatch sig fK) ∧
    ¬ (∃ bytes, sigParamBytes fK.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
    fA2 ∈ (L F0).P.funcs ∧ fW ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fW) ∧
    (∃ info, (L F0).ProgSite fW info fA2) ∧
    Opt.Legalize128.function128Cert (srcFn 9) = .ok (fA2, certOf 9) ∧
    Opt.Legal.check (srcFn 9) fA2 (certOf 9) = true ∧
    Opt.Legalize128.function128Cert (srcFn 10) = .ok (fW, certOf 10) ∧
    Opt.Legal.check (srcFn 10) fW (certOf 10) = true ∧
    (srcFn 9).sig.params.map (·.ty) = [.i128, .i128] ∧ (srcFn 9).sig.returns.map (·.ty) = [.i128] ∧
    fA2.sig.params.map (·.ty) = [.i64, .i64, .i64, .i64] ∧
    fA2.sig.returns.map (·.ty) = [.i64, .i64] ∧
    fS ∈ (L F0).P.funcs ∧ fK ∈ (L F0).P.funcs ∧
    (∃ info ti, (A fF).vcp.TrySite info ti ∧ (L F0).ProgSite fF info fG) ∧
    (∃ info, (L F0).ProgSite fG info fH) ∧
    (∃ info, (L F0).ProgSite fF info fS) ∧ fS.sig.params.any (·.purpose == .sret) = true ∧
    (∃ info, (L F0).ProgSite fF info fK) ∧ (∃ off, ArgLoc.stack off ∈ locsOf fK.sig) ∧
    (RAFrame.compute (A fF).vcp (A fF).rf).intBase ≠ 0 ∧ fF.slots ≠ [] ∧
    fR ∈ (L F0).P.funcs ∧ fRS ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fR) ∧
    (∃ info, (L F0).ProgSite fR info fRS) ∧ (∃ info, (L F0).ProgSite fRS info fR) ∧
    fRS.name = fR.name ++ "__fvself" ∧ fRS.blocks = fR.blocks ∧ fRS.sig = fR.sig ∧
    (A fRS).base = (A fR).base ∧ (A fRS).fb.words = (A fR).fb.words ∧
    (∃ pc, CallPc (A fR).fa (A fR).base pc ∧
      ∃ k < (A fRS).fb.words.size, pc + 4 = (A fRS).base + BitVec.ofNat 64 (4 * k)) ∧
    (∃ pc, CallPc (A fRS).fa (A fRS).base pc ∧
      ∃ k < (A fR).fb.words.size, pc + 4 = (A fR).base + BitVec.ofNat 64 (4 * k)) ∧
    fT ∈ (L F0).P.funcs ∧ fU ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fT) ∧
    fT.slots ≠ [] ∧ (∃ info, (L F0).ProgSite fF info fU) ∧ (∃ info, (L F0).ProgSite fU info fK) ∧
    (RAFrame.compute (A fU).vcp (A fU).rf).intBase ≠ 0 ∧ (L F0).NeedSlots ∧ (L F0).NeedNI ∧
    (L F0).PlaceAt cs0.mem (spv w0) ∧
    fM ∈ (L F0).P.funcs ∧ fD ∈ (L F0).P.funcs ∧ (∃ info, (L F0).ProgSite fF info fD) ∧
    ¬ Clif.IndFree fD ∧ fD.externs = [] ∧ ¬ DeclN fD fM.name ∧
    (∃ info, (A fD).vcp.CallSite info ∧ ∀ n, info.dest ≠ .sym n) ∧
    (L F0).syms fM.name = some 0xE0000 ∧ cs0.mem.symbols "vt" = some vtAddr ∧
    vtObj.items.drop 8 = [.addr "m" 0] ∧ (∃ m, vtWrite = .ok m ∧ cs0.mem.bytes = m.bytes) ∧
    fE ∈ (L F0).P.funcs ∧ Clif.IndFree fE ∧ DeclN fE fS.name ∧ (L F0).P.func? "pz" = none ∧
    (sigRets fS.sig).length = 1 ∧
    (∃ info t Lu Ld, (A fE).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      GotV (A fE).vcp t "pz" ∧ (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    fY ∈ (L F0).P.funcs ∧ ¬ Clif.IndFree fY ∧ (L F0).syms fS.name = some 0x30000 ∧
    ¬ (L F0).MayCall fY fS.name ∧ ¬ (L F0).IndTo fY fS ∧
    (∃ info t Lu Ld, (A fY).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    fZ ∈ (L F0).P.funcs ∧ ¬ Clif.IndFree fZ ∧
    (∃ sig ∈ indSigs fZ, LinkSys.IndTyMatch sig fS ∧ sig.returns.length = fS.sig.returns.length) ∧
    ¬ (L F0).MayCall fZ fS.name ∧ ¬ (L F0).IndTo fZ fS ∧
    (∃ info t Lu Ld, (A fZ).vcp.CallSite info ∧ info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      (regLocs fS.sig).length = Lu.length ∧ Lu.map (·.2) ≠ regLocs fS.sig) ∧
    run0 = .returned [⟨.i64, 802#64⟩] (retMem run0) ∧
    ArmRefines (A fF).fb (A fF).base 8 ((L F0).mach M0 fF) s0 run0 := by
  have hF : ∀ a, Img P A a → F0 a := fun a ha => .inr ha
  have hL := L_ok F0 hF
  have hfF : fF ∈ (L F0).P.funcs := by simp [L, P]
  have hc := callChainB_true
  simp only [callChainB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcf, hcg⟩, hcs⟩, hck⟩, hpg⟩, hph⟩, hps⟩, hpk⟩, hsret⟩, hstk⟩, hcr⟩,
    hcrs⟩, hcfr⟩, hpr⟩, hprs⟩, hnm⟩, hbl⟩, hsg⟩, hcv⟩, hpv⟩, hpq⟩, hreg⟩, hind⟩, hdecl⟩, hsq⟩, hcw⟩,
    hca2⟩, hpw⟩, hpa2⟩, hl9⟩, hl9e⟩, hk9⟩, hl10⟩, hl10e⟩, hk10⟩, hs9p⟩, hs9r⟩, ha2p⟩, ha2r⟩ := hc
  obtain ⟨hbound, hloc, -, hfunc, hentry, hsig, hparams, hset, hret, hvals, hvtw, hnone⟩ :=
    entryFacts
  obtain ⟨hframe, hdrop, hfs, hsb, hib, hsz, hlay, hslots⟩ := frameFacts
  have hrun : run0 = .returned [⟨.i64, 802#64⟩] (retMem run0) := by
    rw [← hvals]; exact eq_returned hret
  have hfa := facts (g := fF) (by simp [P])
  have hlocs : locsOf fF.sig = [.reg (.x 0)] := by
    unfold locB at hloc
    split at hloc
    · assumption
    · cases hloc
  have hbF : (A fF).base.toNat + 4 * (A fF).fb.words.size + 4 ≤ 0xF8000 := bound_of (by simp [P])
  obtain ⟨-, -, -, hns, hnk, -, -, hnq, hnv, -, -, -, -, hnm', hnd, -, -, -⟩ := names
  have hsk := sigChainB_true
  simp only [sigChainB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hsk
  obtain ⟨⟨⟨hsymk, hndk⟩, hnomatch⟩, hbytes⟩ := hsk
  have hgc := gotChainB_true
  simp only [gotChainB, Bool.and_eq_true, decide_eq_true_eq] at hgc
  obtain ⟨⟨⟨⟨⟨-, hpz⟩, hde⟩, hie⟩, hgc'⟩, hsr⟩ := hgc
  have hbc := blrChainB_true
  simp only [blrChainB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hbc
  obtain ⟨⟨⟨⟨⟨-, hiy⟩, hexty⟩, hsyms⟩, hnomatchY⟩, hblrY⟩ := hbc
  have hniY : ¬ Clif.IndFree fY := fun h => by rw [indFreeB_of h] at hiy; cases hiy
  have hzc := zChainB_true
  simp only [zChainB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hzc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hiz⟩, hextz⟩, -⟩, -⟩, hanyZ⟩, hnoZ⟩, hblrZ⟩ := hzc
  have hniZ : ¬ Clif.IndFree fZ := fun h => by rw [indFreeB_of h] at hiz; cases hiz
  have hpS : (L F0).P.func? fS.name = some fS := by show P.func? fS.name = some fS; rw [hns]; exact hps
  have hnmY : ¬ (L F0).MayCall fY fS.name := by
    rintro (hd | ⟨-, -, hall⟩)
    · have h1 := hd.1; rw [hexty] at h1; simp at h1
    · obtain ⟨sig, hs, hm⟩ := hall fS hpS
      exact hnomatchY sig hs hm
  have hnmZ : ¬ (L F0).MayCall fZ fS.name := by
    rintro (hd | ⟨-, -, hall⟩)
    · have h1 := hd.1; rw [hextz] at h1; simp at h1
    · obtain ⟨sig, hs, hm⟩ := hall fS hpS
      exact hnoZ sig hs hm
  have hnmV : ¬ (L F0).MayCall fV fK.name := by
    rintro (hd | ⟨-, -, hall⟩)
    · have := declB_of hd; rw [hnk, hndk] at this; cases this
    · obtain ⟨sig, hs, hm⟩ := hall fK (by show P.func? fK.name = some fK; rw [hnk]; exact hpk)
      exact hnomatch sig hs hm.ty
  have hvt := vtChainB_true
  simp only [vtChainB, Bool.and_eq_true, decide_eq_true_eq] at hvt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcd, hpd⟩, hpm⟩, hregD⟩, hindD⟩, hextD⟩, hsm⟩, hsvt⟩, hdrop8⟩ := hvt
  have hextD' : fD.externs = [] := by simpa using hextD
  have hsc := slotChainB_true
  simp only [slotChainB, Bool.and_eq_true, decide_eq_true_eq] at hsc
  obtain ⟨⟨⟨⟨⟨⟨⟨hct, hcu⟩, hcuk⟩, hpt⟩, hpu⟩, hslT⟩, hibU⟩, -⟩ := hsc
  have hslT' : fT.slots ≠ [] := fun h => by simp [h] at hslT
  have hsT : ∃ info, (L F0).ProgSite fF info fT := by
    obtain ⟨info, hs, hd⟩ := callsB_sound hct
    exact ⟨info, hs, "t", hd, hpt⟩
  have hsU : ∃ info, (L F0).ProgSite fF info fU := by
    obtain ⟨info, hs, hd⟩ := callsB_sound hcu
    exact ⟨info, hs, "u", hd, hpu⟩
  have hsUK : ∃ info, (L F0).ProgSite fU info fK := by
    obtain ⟨info, hs, hd⟩ := callsB_sound hcuk
    exact ⟨info, hs, "k", hd, hpk⟩
  have hNS : (L F0).NeedSlots := ⟨fF, hfF, fT, .inl hsT, hslT'⟩
  have hNN : (L F0).NeedNI := ⟨fF, hfF, fU, .inl hsU, .inl hibU⟩
  have hplace : (L F0).PlaceAt cs0.mem (spv w0) := ⟨[], by rw [spv_w0, frames_eq]; rfl⟩
  have hone := oneCopyB_true
  simp only [oneCopyB, Bool.and_eq_true, decide_eq_true_eq] at hone
  obtain ⟨⟨⟨hob, how⟩, hri1⟩, hri2⟩ := hone
  have hcert : ∀ i g, (Opt.Legalize128.function128Cert (srcFn i)).toBool = true →
      (getOk (Opt.Legalize128.function128Cert (srcFn i))).1 = g →
      Opt.Legalize128.function128Cert (srcFn i) = .ok (g, certOf i) := by
    intro i g h1 h2
    rw [getOk_eq h1, ← h2]
    rfl
  refine ⟨hL, hfF, by simp [L, P], by simp [L, P], by simp [L, P], by simp [L, P], ?_,
    fun h => (by rw [indFreeB_of h] at hind; cases hind), ?_,
    (by rw [hnq]; exact declB_sound hdecl), (by simp only [L, hnq]; exact hsq),
    (by simp only [L, hnk]; exact hsymk), hnmV,
    hnomatch, fun ⟨b, hb, hb8⟩ => by rw [hb] at hbytes; simp at hbytes; omega,
    by simp [L, P], by simp [L, P], ?_, ?_, hcert 9 fA2 hl9 hl9e, hk9, hcert 10 fW hl10 hl10e, hk10,
    hs9p, hs9r, ha2p, ha2r,
    by simp [L, P], by simp [L, P], ?_, ?_, ?_,
    hsret, ?_, ?_, by rw [hib]; decide, fun h => by simp [h] at hslots, by simp [L, P],
    by simp [L, P], ?_, ?_, ?_, hnm, hbl, hsg, hob, how, retIntoB_sound hri1, retIntoB_sound hri2,
    by simp [L, P], by simp [L, P], hsT, hslT', hsU, hsUK,
    hibU, hNS, hNN, hplace, by simp [L, P], by simp [L, P], ?_,
    fun h => (by rw [indFreeB_of h] at hindD; cases hindD), hextD',
    (fun h => by have h1 := h.1; rw [hextD'] at h1; simp at h1), regCallsB_sound hregD,
    (by simp only [L, hnm']; exact hsm), (by show symsW "vt" = some vtAddr; exact hsvt), hdrop8,
    ?_, by simp [L, P], indFreeB_sound hie, (by rw [hns]; exact declB_sound hde), hpz, hsr,
    gotCallB_sound hgc', by simp [L, P], hniY, (by simp only [L, hns]; exact hsyms), hnmY,
    (fun ⟨hm, _⟩ => hnmY hm), blrArgsB_sound hblrY, by simp [L, P], hniZ, hanyZ, hnmZ,
    (fun ⟨hm, _⟩ => hnmZ hm), blrArgsB_sound hblrZ, hrun, ?_⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcv
    exact ⟨info, hs, "v", hd, hpv⟩
  · exact regCallsB_sound hreg
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcw
    exact ⟨info, hs, "w", hd, hpw⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hca2
    exact ⟨info, hs, "a2", hd, hpa2⟩
  · obtain ⟨info, ti, hs, hd⟩ := tryCallsB_sound hcf
    exact ⟨info, ti, hs, hs.callSite, "g", hd, hpg⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcg
    exact ⟨info, hs, "h", hd, hph⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcs
    exact ⟨info, hs, "s", hd, hps⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hck
    exact ⟨info, hs, "k", hd, hpk⟩
  · obtain ⟨l, hl, hst⟩ := List.any_eq_true.mp hstk
    cases l with
    | stack off => exact ⟨off, hl⟩
    | reg _ => cases hst
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcfr
    exact ⟨info, hs, "r", hd, hpr⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcr
    exact ⟨info, hs, "r__fvself", hd, hprs⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcrs
    exact ⟨info, hs, "r", hd, hpr⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcd
    exact ⟨info, hs, "d", hd, hpd⟩
  · revert hvtw
    unfold vtWriteOk
    split
    · rename_i m hm
      intro _
      exact ⟨m, hm, by simp [cs0, memV, hm]⟩
    · intro h; cases h
  rw [hrun]
  refine backend_correct_program_returned (L F0) hL hfF M0 (w₀ := w0) (args := [arg]) (cs := cs0)
    ?hent ?hres rfl ?hgfree ?himg ?hbe ?hargs ?hcs ?hsav ?hrel (fun _ => hplace) (hrun ▸ rfl)
  case hent =>
    refine ⟨s0_program, imgCode_of (okB_imgB) (by simp [P]) s0 (fun a ha => s0_img ha),
      by simp [s0, L, Arm.r_of_w_same], ?_, ?_, hL.raStar fF hfF, ?_, hL.fits fF hfF⟩
    · simp [s0, Arm.r_of_w_different, r_setMem, r_set_program, Arm.r, Arm.read_base_error,
        Arm.ArmState.default]
    · simp [s0, xreg, Arm.r_of_w_different, Arm.r_of_w_same]
    · rw [spv_s0]; decide
  case hres =>
    refine ⟨by simp [L, LinkSys.K, hfs, spv_s0, sp0, M0], fun a ha => ?_⟩
    have hlt := codeAddr_lt hbF s0_program ha
    simp only [L, LinkSys.K, hfs, spv_s0, sp0, M0]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (1048576 : BitVec 64).toNat = 1048576 := rfl
    omega
  case hgfree =>
    intro a ha ⟨h1, h2⟩
    have hlt := img_lt ha
    simp only [L, LinkSys.K, hdrop, spv_s0, sp0, M0] at h1 h2
    simp at h2
    omega
  case himg => exact fun a ha => s0_img ha
  case hbe =>
    refine ⟨?_, ?_, fun i hi => ?_, fun i _ => ?_, fun f _ h29 h31 => ?_, ?_, ?_⟩
    · simp only [L, hdrop, spv_s0]; simp [w0, spv, Arm.r_of_w_same]
    · simp only [L, hframe, ite_true, spv_s0]; simp [w0, xreg, Arm.r_of_w_different, Arm.r_of_w_same]
    · simp only [xreg, w0]
      rw [Arm.r_of_w_different (gpr_ne (by omega) (by omega) (by omega : i ≠ 31)),
        Arm.r_of_w_different (gpr_ne (by omega) (by omega) (by omega : i ≠ 29))]
    · simp [w0, Arm.r_of_w_different]
    · simp only [w0]; rw [Arm.r_of_w_different h31, Arm.r_of_w_different h29]
    · simp [w0, mem_w]
    · simp [w0, Arm.w_program]
  case hargs =>
    intro loc v hm
    rw [hlocs] at hm
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [VHolds, regVal, rnum, s0, Arm.r_of_w_different, Arm.r_of_w_same, arg]
  case hcs =>
    refine ⟨rfl, rfl, hsig, ⟨bF, hentry, rfl, rfl, hparams, ?_⟩, by simp [cs0, hslots]⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hset
    simp only [cs0, hr, Option.getD_some]
  case hsav =>
    intro off v hm
    rw [hlocs] at hm
    simp at hm
  case hrel =>
    have hvalid : ∀ a n, cs0.mem.valid a n = true →
        (slotAddr ≤ a ∧ a + n ≤ slotAddr + 8) ∨ (vtAddr ≤ a ∧ a + n ≤ vtAddr + 16) := by
      intro a n h
      simp [cs0, memV, mem0, Clif.Mem.valid, Clif.Alloc.contains] at h
      omega
    have hw : w0.mem = memS := by simp [w0, mem_w, s0_mem]
    refine ⟨⟨fun a b ha hb => ?_, fun a n ha => ?_, rfl⟩, fun id b h => ?_, ?_⟩
    · change memV.bytes a = some b at hb
      rcases hvalid a 1 ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hnone (a - slotAddr) (by omega)
        rw [show slotAddr + (a - slotAddr) = a by omega, hb] at this
        cases this
      · have ht : (BitVec.ofNat 64 a).toNat = a := by
          simp only [BitVec.toNat_ofNat, vtAddr] at h2 ⊢; omega
        simp only [Arm.read_mem, Arm.read_store, hw, memS, ht]
        rw [if_pos ⟨h1, by omega⟩, hb]
        rfl
    · rcases hvalid a n ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨by simp [slotAddr] at h2 ⊢; omega, fun k hk => not_F0 ?_ ?_ ?_ ?_⟩ <;>
          simp only [BitVec.toNat_ofNat, slotAddr] at h1 h2 ⊢ <;>
          rw [Nat.mod_eq_of_lt (by omega)] <;> omega
      · refine ⟨by simp [vtAddr] at h2 ⊢; omega, fun k hk => not_F0_vt ?_ ?_⟩ <;>
          simp only [BitVec.toNat_ofNat, vtAddr] at h1 h2 ⊢ <;>
          rw [Nat.mod_eq_of_lt (by omega)] <;> omega
    · simp only [cs0, List.lookup] at h
      split at h
      · rename_i e
        cases h
        have hid : id = 0 := by simpa using e
        subst hid
        refine ⟨0, by rw [hlay]; rfl, ?_⟩
        simp only [Rel.slotReg, spv_w0, sp0, slotAddr]
        rw [show ((L F0).A fF) = A fF from rfl, hsb]
        decide
      · cases h
    · show OutRel _ (RAFrame.compute (A fF).vcp (A fF).rf).intBase _ _
      rw [hib]
      refine ⟨by decide, fun j hj => not_F0 ?_ ?_ ?_ ?_, fun a n ha k hk j hj e => ?_⟩
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0] at e
        have := congrArg BitVec.toNat e
        rcases hvalid a n ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [sp0, slotAddr] at this h1 h2
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          bv_omega
        · simp only [sp0, vtAddr] at this h1 h2
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          bv_omega

/-! ## The legalised callee against its `i128` source -/

/-- `a2` (source and legalisation) declares nothing, has no indirect call, no `try_call` and no
call site in its compiled code. -/
def a2B : Bool :=
  (srcFn 9).externs.isEmpty && fA2.externs.isEmpty && indFreeB (srcFn 9) && indFreeB fA2 &&
  fA2.blocks.all (fun b => !b.term.isTry) &&
  allInsts (A fA2).vcp (fun i => match i with | .call _ | .tryCall _ _ => false | _ => true) &&
  Opt.Legal.check (srcFn 9) fA2 (certOf 9)

theorem a2B_true : a2B = true := by native_decide

/-- **The composition with `backend_correct_legal`** for the program's legalised callee `a2`:
the code linked into the witness program (`A fA2`, compiled from the legalisation `fA2` the
validator accepts) refines, by `backend_correct_legal`, the run of the ORIGINAL `i128` function
`a2` — its arguments and results ABI-split into register pairs. Every function-level premise is
discharged (callee-free: the callee contracts are vacuous with the base hooks); the entry
premises remain. In the linked program the same code is reached by `w`'s `bl a2` with the pairs in
x0–x3 (`backend_correct_program_witness`): `backend_correct_program` relates the Arm run to the
legalised program, this theorem the callee to its `i128` source. -/
theorem a2_legal {F : BitVec 64 → Prop} {p : Clif.Program} {K : Nat}
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry (A fA2).fb base ra s) (hres : StackAvail K (A fA2).af s)
    (hbe : BodyEntry (A fA2).af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups (srcFn 9).sig.params).getD []) args args')
    (hargs : ArgsIn fA2.sig args' s) (hcs : ClifEntry (srcFn 9) args cs)
    (hcs' : ClifEntry fA2 args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
      (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af s, fun _ => none,
      (A fA2).af.slotBase, (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2
      cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env ((L F).P.only fA2) cs') (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups (srcFn 9).sig.returns).getD []) (A fA2).fb base ra
      (ArmStepX Xb Hb (A fA2).fa) s (Clif.runLoop Clif.Rust.env p fuel cs) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hfa := facts hA2
  have ha := a2B_true
  simp only [a2B, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨he9, heA⟩, hi9⟩, hiA⟩, hnt⟩, hnc⟩, hchk⟩ := ha
  refine backend_correct_legal (X := Xb) (H := Hb) (syms := fun _ => none)
    (slotOff := (A fA2).af.slotBase) (K := K) hchk (hL.subset fA2 hA2) (hL.compiled fA2 hA2)
    (fun fn e h => by simp [Clif.Function.extern?, he9] at h)
    (fun fn e h => by simp [Clif.Function.extern?, heA] at h)
    (fun ⟨B, hB, st, hst, sig, callee, args, hi⟩ =>
      absurd hi ((indFreeB_sound hi9 B hB).1 st hst sig callee args))
    (hL.covered fA2 hA2) (fun _ => ⟨fun ctx info hsite => ?_, fun d u _ _ => by
      simp [Hb, Arm.r_of_w_same], fun d uses w outs w' hx _ => by simp [Xb] at hx⟩)
    (fun ⟨B, hB, ht⟩ => absurd ht (by simpa using hnt B hB))
    (fun ht => absurd ht (by simp [hfa.tls]))
    (fun _ ext hin => by simp [heA] at hin)
    (fun _ => by rw [indSigs_nil_of_indFree (indFreeB_sound hiA)]; exact xCallsIndOk_nil _ _ _)
    (fun n b h => by cases h) rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel
  obtain ⟨b, vb, k, hb, hk | ⟨ti, hk⟩⟩ := hsite
  · have := allInsts_sound hnc hb hk; simp at this
  · have := allInsts_sound hnc hb hk; simp at this

end E2E.LinkWitness
