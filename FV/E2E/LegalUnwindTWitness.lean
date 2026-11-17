import FV.Opt.Proof.LegalSimX2T
import FV.E2E.LegalUnwindWitness

/-!
# Non-vacuity of `checkW_refinesXT` (#1076)

The witness function, an `i128` function whose `try_call_indirect` callee raises into its
handler (the shape of Rust's `Box<dyn Any>::downcast`: an `i128` value and an indirect call with
an `i128`-free signature); it is outside `legalOkB` (no `try_call_indirect` there) and inside
`legalOkTB` (`domains`):

```
function %wt(i128, i64) system_v {
    sig0 = (i64) system_v
block0(v0: i128, v1: i64):
    try_call_indirect v1(v1), sig0, block1, [ tag0: block2(exn0) ]
block1:
    return
block2(v2: i64):
    return
}
```

Its legalisation (`legal_eq`) splits `v0` into `v4`, `v5` and adds the pad zero `v6`; `checkW` and
`exnOkT` accept it, and its indirect call has an `i128`-free signature (`validators`). The
environment is the trusted Rust environment with unwinding `Clif.Rust.xenvWith raises 77`
(`raises := (· == "throw")`) whose name list holds `%throw`, the memory places `%throw` at
`4096`: the callee `v1 = 4096` resolves to `%throw`, which raises Rust's exception (object 77)
(`raises_here`), the `tag0` handler catches it and the run returns (`caught`).

* `refines`: `Opt.Legal.X.checkW_refinesXT` applies with every premise discharged; the target
  run returns too.
-/

namespace Clif.Rust.LegalXTWitness

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128
open Clif.Rust.LegalXWitness (func?_nil noMemTrapX_of_nil noIndInternalX_of_nil)

def i128p : AbiParam := { ty := .i128 }
def i64p : AbiParam := { ty := .i64 }
def sigP : Signature := { params := [i128p, i64p], returns := [], callConv := some .systemV }
def sigI : Signature := { params := [i64p], returns := [], callConv := some .systemV }
def sigL : Signature := { params := [i64p, i64p, i64p], returns := [], callConv := some .systemV }

def et : ExnTable :=
  { sig := 0, normal := { block := 1, args := [] }, items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- The source: `try_call_indirect v1(v1)`, a `tag0` handler. -/
def src : Function :=
  { name := "wt", sig := sigP, externs := [], sigDecls := [(0, sigI)],
    blocks := [
      { id := 0, params := [(0, .i128), (1, .i64)], term := .tryCallIndirect 1 [1] et },
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(2, .i64)], term := .ret [] }] }

/-- The legalisation's entry block: the halves `v4`, `v5`, `v1`, the pad zero `v6`. -/
def b0' : Block :=
  { id := 0, params := [(4, .i64), (5, .i64), (1, .i64)],
    body := [{ results := [6], inst := .iconst .i64 0 }], term := .tryCallIndirect 1 [1] et }

/-- The legalisation. -/
def gL : Function :=
  { name := "wt", sig := sigL, externs := [], sigDecls := [(0, sigI)],
    blocks := [b0',
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(2, .i64)], term := .ret [] }] }

/-- Its certificate: `v0` is split into `v4`, `v5`; the pad zero is `v6`. -/
def certL : Cert := { pairs := [(0, 4, 5)], zero := 6 }

/-- **The legalisation pass computes `gL`, `certL`.** -/
theorem legal_eq : function128Cert src = .ok (gL, certL) := by
  have h : (function128Cert src).toOption.map (fun r => (r.1, r.2.pairs, r.2.zero)) =
      some (gL, certL.pairs, certL.zero) := by native_decide -- witness: native_decide
  cases hc : function128Cert src with
  | error e => rw [hc] at h; simp [Except.toOption] at h
  | ok r =>
    rw [hc] at h
    obtain ⟨g, c⟩ := r
    obtain ⟨ps, z⟩ := c
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-- `src` is outside the old source domain (`legalOkB`) and inside the new one (`legalOkTB`). -/
theorem domains : legalOkB src = false ∧ legalOkTB src = true := by
  native_decide -- witness: native_decide

def C : Ctx := ⟨src, gL, certL⟩

theorem validators : checkW C.f C.g C.cert = true ∧ exnOkT C.f C.g C.cert = true ∧
    indTB C.f = true := by
  decide +kernel

def raises (n : String) : Bool := n == "throw"

/-- `Clif.Rust.xenvWith raises 77` with `%throw` in its name list. -/
def xe : XEnv := { xenvWith raises 77 with names := ["throw"] }

/-- The memory: `%throw` at `4096`. -/
def mem0 : Mem := { symbols := fun n => if n == "throw" then some 4096 else none }

/-- The source frame on the arguments `5 : i128`, `4096`. -/
def fr0 : Frame :=
  { func := src, regs := (Regs.empty.setMany [0, 1] [⟨.i128, 5⟩, ⟨.i64, 4096⟩]).getD Regs.empty,
    slots := [], body := [], term := .tryCallIndirect 1 [1] et }

/-- The target frame on the halves `5`, `0` and `4096`. -/
def fr0' : Frame :=
  { func := gL,
    regs := (Regs.empty.setMany [4, 5, 1] [⟨.i64, 5⟩, ⟨.i64, 0⟩, ⟨.i64, 4096⟩]).getD Regs.empty,
    slots := [], body := b0'.body, term := b0'.term }

/-- **The `try_call_indirect`'s callee raises** at the source's first step. -/
theorem raises_here : (raiseAt? xe { funcs := [] } ⟨fr0, [], mem0⟩).isSome = true := by
  decide +kernel

/-- **The source run with unwinding raises and catches**: `%throw` raises, the `tag0` handler
catches, the run returns. -/
theorem caught :
    (runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], mem0⟩, []⟩).returnedVals? = some [] := by
  decide +kernel

theorem envOk : EnvOkX xe C { funcs := [] } { funcs := [] } where
  base :=
    { src := fun _ _ _ => func?_nil _
      tgt := fun _ _ _ => func?_nil _
      helper := xenvWith_helperOk raises 77
      ext := xenvWith_extLegal raises 77
      keep := xenvWith_envKeepsAllocs raises 77
      ind := fun _ => ⟨rfl, List.prefix_refl _⟩
      sigs := fun h => absurd h (S.indTB_not_ind128 validators.2.2) }
  extX := xenvWith_extLegalX raises 77
  keepX := xenvWith_envKeepsAllocsX raises 77
  arity := xenvWith_exnArityOk raises 77

/-- **`checkW_refinesXT` applies** to the raising-and-catching run with every premise discharged:
the target run with unwinding returns too. -/
theorem refines : ∃ vals' k M, runLoopX xe { funcs := [] } k ⟨⟨fr0', [], mem0⟩, []⟩ =
    .returned vals' M := by
  obtain ⟨hc, hx, hT⟩ := validators
  have hfb : ∀ B ∈ src.blocks, B.body = [] := by
    intro B hB
    simp only [src, List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> rfl
  have hg : groups C.f.sig.params = some [[.lo, .hi], [.val i64p]] := rfl
  have hexp : ExpRel ((groups C.f.sig.params).getD []) [⟨.i128, 5⟩, ⟨.i64, 4096⟩]
      [⟨.i64, 5⟩, ⟨.i64, 0⟩, ⟨.i64, 4096⟩] := by
    rw [hg]
    exact ⟨⟨5, 0, rfl, rfl, rfl⟩, rfl, trivial⟩
  have h := checkW_refinesXT (C := C) hc hx hT envOk (b := src.blocks.head!) (b' := b0')
    (args := [⟨.i128, 5⟩, ⟨.i64, 4096⟩]) (args' := [⟨.i64, 5⟩, ⟨.i64, 0⟩, ⟨.i64, 4096⟩])
    (fr0 := fr0) (fr0' := fr0') (m := mem0) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hexp
    (fun a n h => by simp [Mem.valid, mem0] at h)
    (noMemTrapX_of_nil hfb rfl rfl) (noIndInternalX_of_nil hfb rfl rfl) 10
  obtain ⟨M, hM⟩ : ∃ M, runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], mem0⟩, []⟩ = .returned [] M := by
    have := caught
    revert this
    cases runLoopX xe { funcs := [] } 10 ⟨⟨fr0, [], mem0⟩, []⟩ <;> simp [XOutcome.returnedVals?]
  obtain ⟨vals', -, k, hk⟩ := h.1 [] M hM
  exact ⟨vals', k, M, hk⟩

end Clif.Rust.LegalXTWitness
