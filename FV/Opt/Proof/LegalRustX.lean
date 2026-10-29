module

public import FV.Opt.Proof.LegalSimX
public import FV.Opt.Proof.LegalRust

@[expose] public section

/-!
# The trusted Rust environment with unwinding (S10e, #232)

`Clif.Rust.xenvWith raises obj`: `Clif.Rust.env` with unwinding externs. The `__*ti3` helpers
are `Clif.Rust.env`'s (they never unwind); an extern `raises` classifies raises Rust's exception
`panicExn obj`, caught by `tag 0` (cleanup) and `tag 1` (catch-all) handlers, payload `[obj, 0]`
(the exception object and the selector Rust's personality installs, S10d), the memory
unchanged; every other extern is `Clif.Rust.env`'s. `Clif.Rust.xenv obj` (`panic=unwind`):
the diverging entry points (`isPanic`) raise instead of trapping.

The contracts of the refinement theorem with unwinding (`Opt.Legal.X.check_refinesX`) hold:
`HelperOk`/`ExtLegal`/`EnvKeepsAllocs` of `xenv.toEnv` (off the panic names `xenv.toEnv` is
`Clif.Rust.env`; a panic is `stuck` there, which those contracts do not constrain), and
`ExtLegalX`/`EnvKeepsAllocsX`/`ExnArityOk` of `xenv` (only a panic unwinds, with the same
exception and memory whatever its arguments).
-/

namespace Clif.Rust

open Opt.Legal Opt.Legal.X Opt.Legalize128

/-- Rust's exception with exception object `obj`, as Rust's personality treats it: caught by
`tag 0` and `tag 1` handlers, payload `[obj, 0]`. -/
def panicExn (obj : BitVec 64) : Exn where
  catches n := n == 0 || n == 1
  payload := [⟨.i64, obj⟩, ⟨.i64, 0⟩]

/-- **The trusted Rust environment with unwinding externs `raises`**: such an extern raises
`panicExn obj`; the helpers and every other extern are `Clif.Rust.env`'s. -/
def xenvWith (raises : String → Bool) (obj : BitVec 64) : XEnv where
  extern name :=
    if isDivHelper name then
      some fun vals m => (divOutcome name vals m).toX
    else if raises name then
      some fun _ m => .unwound (panicExn obj) m
    else (env.extern name).map fun g vals m => (g vals m).toX

/-- **The trusted Rust environment with unwinding** (`panic=unwind`): a diverging entry point
raises `panicExn obj`. -/
def xenv (obj : BitVec 64) : XEnv := xenvWith isPanic obj

/-- Off the raising names, `xenvWith`'s externs are `env`'s. -/
theorem xenvWith_toEnv_extern (raises : String → Bool) (obj : BitVec 64) {name : String}
    (h : isDivHelper name = true ∨ raises name = false) :
    (xenvWith raises obj).toEnv.extern name = env.extern name := by
  simp only [XEnv.toEnv, xenvWith]
  by_cases hd : isDivHelper name = true
  · simp [hd, env]
  · have hp : raises name = false := by simpa [hd] using h
    simp only [hd, Bool.false_eq_true, ite_false, hp]
    cases env.extern name <;> simp

/-- At a raising name `xenvWith.toEnv`'s extern is `stuck`. -/
theorem xenvWith_toEnv_raise (raises : String → Bool) (obj : BitVec 64) {name : String}
    (hd : isDivHelper name = false) (hp : raises name = true) :
    (xenvWith raises obj).toEnv.extern name =
      some fun _ _ => .stuck "callee unwound (Clif.run has no unwinding)" := by
  simp [XEnv.toEnv, xenvWith, hd, hp, XOutcome.toOutcome]

theorem xenvWith_helperOk (raises : String → Bool) (obj : BitVec 64) :
    HelperOk (xenvWith raises obj).toEnv := by
  intro op
  rw [xenvWith_toEnv_extern raises obj (.inl (isDivHelper_divHelper op))]
  exact helperOk_env op

theorem xenvWith_extLegal (raises : String → Bool) (obj : BitVec 64) :
    ExtLegal (xenvWith raises obj).toEnv := by
  intro name h hext sig gs rg hgs hrg vals vals' m hty hexp
  by_cases hq : isDivHelper name = true ∨ raises name = false
  · rw [xenvWith_toEnv_extern raises obj hq] at hext
    exact extLegal_env name h hext sig gs rg hgs hrg vals vals' m hty hexp
  · simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at hq
    rw [xenvWith_toEnv_raise raises obj hq.1 hq.2] at hext
    cases hext
    exact ⟨(fun _ _ h _ => by simp at h), (fun _ h => by simp at h)⟩

theorem xenvWith_envKeepsAllocs (raises : String → Bool) (obj : BitVec 64) :
    EnvKeepsAllocs (xenvWith raises obj).toEnv := by
  intro name h hext vals m rv m' hr
  by_cases hq : isDivHelper name = true ∨ raises name = false
  · rw [xenvWith_toEnv_extern raises obj hq] at hext
    exact envKeepsAllocs_env name h hext vals m rv m' hr
  · simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at hq
    rw [xenvWith_toEnv_raise raises obj hq.1 hq.2] at hext
    cases hext
    simp at hr

/-- Only a raising extern unwinds, with `panicExn obj` and the caller's memory. -/
theorem xenvWith_unwound {raises : String → Bool} {obj : BitVec 64} {name : String}
    {h : List Val → Mem → XOutcome} (hext : (xenvWith raises obj).extern name = some h)
    {vals : List Val} {m : Mem} {e : Exn} {m' : Mem} (hu : h vals m = .unwound e m') :
    (∀ vals', h vals' m = .unwound (panicExn obj) m) ∧ e = panicExn obj ∧ m' = m := by
  simp only [xenvWith] at hext
  split at hext
  · cases hext; exact absurd hu (Outcome.toX_ne_unwound _ _ _)
  · split at hext
    · cases hext
      simp only [XOutcome.unwound.injEq] at hu
      exact ⟨fun _ => rfl, hu.1.symm, hu.2.symm⟩
    · obtain ⟨g0, -, rfl⟩ := Option.map_eq_some_iff.mp hext
      exact absurd hu (Outcome.toX_ne_unwound _ _ _)

theorem xenvWith_extLegalX (raises : String → Bool) (obj : BitVec 64) :
    ExtLegalX (xenvWith raises obj) := by
  intro name h hext sig gs hgs vals vals' m hty hexp e m' hu
  obtain ⟨hall, rfl, rfl⟩ := xenvWith_unwound hext hu
  exact hall vals'

theorem xenvWith_envKeepsAllocsX (raises : String → Bool) (obj : BitVec 64) :
    EnvKeepsAllocsX (xenvWith raises obj) := by
  intro name h hext vals m e m' hu
  obtain ⟨-, -, rfl⟩ := xenvWith_unwound hext hu
  rfl

theorem xenvWith_exnArityOk (raises : String → Bool) (obj : BitVec 64) :
    ExnArityOk (xenvWith raises obj) := by
  intro name h hext vals m e m' hu
  obtain ⟨-, rfl, -⟩ := xenvWith_unwound hext hu
  simp [panicExn]

/-- The environment's side of `check_refinesX` for `xenvWith`, from the programs' conditions (on
the domain of `check`, `indOldB`: every indirect call site is a `call_indirect` at a signature
without `i128`). -/
theorem xenvWith_envOkX (raises : String → Bool) (obj : BitVec 64) {C : Ctx} {p p' : Program}
    (hold : indOldB C.f = true)
    (hsrc : ∀ fn e, C.f.extern? fn = some e → p.func? e.name = none)
    (htgt : ∀ fn e, C.g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ B ∈ C.f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
      st.inst = .callIndirect sig callee args) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames) :
    EnvOkX (xenvWith raises obj) C p p' where
  base := ⟨hsrc, htgt, xenvWith_helperOk raises obj, xenvWith_extLegal raises obj,
    xenvWith_envKeepsAllocs raises obj, indOldB_ind hold hind, indOldB_sigs hold⟩
  extX := xenvWith_extLegalX raises obj
  keepX := xenvWith_envKeepsAllocsX raises obj
  arity := xenvWith_exnArityOk raises obj


end Clif.Rust
