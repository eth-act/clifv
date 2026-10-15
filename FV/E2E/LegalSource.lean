import FV.E2E.LegalProgram
import FV.E2E.LinkScopeDefs
import FV.Opt.Legalize128Pre

/-!
# The original source program of an input (S2/S3 provenance)

`FnInput.func` is the function `lean-backend` compiles: the parsed function after the `i128`
legalisation (`Opt.Legalize128.parsedFile128`). `FnInput.src` is the function as parsed, and
`FnInput.func_eq`: `fi.func = legalize fi.src` for every input (`parsedFile128` keeps a function
whose legalisation fails, `legalize` too). So the program of an input is the legalisation of its
source program: `LinkInput.prog_eq : I.prog = legalProg I.srcProg`.

`SrcScopeB I`: **the source domain** of an input, decided on the parsed functions: every
function in `legalOkB` (the pass is the identity, or `Opt.Legal.Complete.Pre` holds and the
pass succeeds — no validator involved), no `return_call`, the declarations of the program's
functions with their signatures, no function named like a `__*ti3` helper. With `InScopeP` (on
the legalised program, which `compileExe` checks) it gives `E2E.LegalProgram.ProgCtx`, the
domain of the whole-program refinement `legalProg_refines` (`srcCtx`).
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128 E2E.LegalProgram

/-- The function the file holds at index `k`, as parsed (before the `i128` legalisation). -/
def FnInput.src (fi : FnInput) : Clif.Function :=
  match (Clif.parseFile fi.clif).funcs[fi.k]? with
  | some p => getOk p.func
  | none => default

/-- **The source program** of an input: its parsed functions. -/
def LinkInput.srcProg (I : LinkInput) : Clif.Program := { funcs := I.funcs.map (·.src) }

/-- One parsed function as `parsedFile128` leaves it. -/
def legalizeParsed (p : Clif.ParsedFunction) : Clif.ParsedFunction :=
  match p.func with
  | .ok f =>
    match function128Cert f with
    | .ok (f', _) => if f' == f then p else { p with func := .ok f' }
    | .error _ => p
  | .error _ => p

theorem foldl_file {F : Legalized → Clif.ParsedFunction → Legalized}
    {g : Clif.ParsedFunction → Clif.ParsedFunction}
    (hF : ∀ acc p, (F acc p).file.funcs = acc.file.funcs ++ [g p]) :
    ∀ (l : List Clif.ParsedFunction) (acc : Legalized),
      (l.foldl F acc).file.funcs = acc.file.funcs ++ l.map g
  | [], acc => by simp
  | p :: l, acc => by
    rw [List.foldl_cons, foldl_file hF l, hF, List.map_cons, List.append_assoc]
    rfl

/-- `parsedFile128` replaces every function by its legalisation, in order. -/
theorem parsedFile128_funcs (pf : Clif.ParsedFile) :
    (parsedFile128 pf).file.funcs = pf.funcs.map legalizeParsed := by
  unfold parsedFile128
  rw [foldl_file (g := legalizeParsed) ?_ pf.funcs]
  · rfl
  · intro acc p
    simp only [legalizeParsed]
    cases hp : p.func with
    | error e => rfl
    | ok f =>
      cases hc : function128Cert f with
      | error e => simp only [hc]
      | ok gc =>
        obtain ⟨f', cert⟩ := gc
        by_cases he : (f' == f) = true
        · simp only [hc, he, ite_true]
        · simp only [hc, he, Bool.false_eq_true, ite_false]
          split <;> rfl

theorem legalize_default : legalize (default : Clif.Function) = default :=
  Opt.Legal.Complete.legalize_of_not_mentions (by decide)

theorem getOk_legalizeParsed (p : Clif.ParsedFunction) :
    getOk (legalizeParsed p).func = legalize (getOk p.func) := by
  cases hp : p.func with
  | error e => simp only [legalizeParsed, hp, getOk]; exact legalize_default.symm
  | ok f =>
    cases hc : function128Cert f with
    | error e => simp [legalizeParsed, getOk, legalize, hc, hp]
    | ok gc =>
      obtain ⟨f', cert⟩ := gc
      by_cases he : f' = f
      · subst he
        simp [legalizeParsed, getOk, hp, hc, Opt.Legal.Complete.legalize_of_ok hc]
      · simp [legalizeParsed, getOk, hp, hc, he, Opt.Legal.Complete.legalize_of_ok hc]

/-- **The compiled function is the legalisation of the parsed one.** -/
theorem FnInput.func_eq (fi : FnInput) : fi.func = legalize fi.src := by
  unfold FnInput.func FnInput.src
  rw [parsedFile128_funcs, List.getElem?_map]
  cases (Clif.parseFile fi.clif).funcs[fi.k]? with
  | none => exact legalize_default.symm
  | some p => exact getOk_legalizeParsed p

/-- **The program of an input is the legalisation of its source program.** -/
theorem LinkInput.prog_eq (I : LinkInput) : I.prog = legalProg I.srcProg := by
  simp only [LinkInput.prog, legalProg, LinkInput.srcProg, List.map_map]
  congr 1
  exact List.map_congr_left fun fi _ => FnInput.func_eq fi

/-! ## The source domain -/

/-- No function of `P` is named like a `__*ti3` helper. -/
def helperFreeB (P : Clif.Program) : Bool :=
  [DivOp.udiv, DivOp.sdiv, DivOp.urem, DivOp.srem].all fun op => (P.func? (divHelper op)).isNone

/-- **The source domain of an input** (decided on its parsed functions): every function in
`legalOkB`, no `return_call`, the declarations of the program's functions with their
signatures, no function named like a `__*ti3` helper. -/
def SrcScopeB (I : LinkInput) : Bool :=
  I.srcProg.funcs.all legalOkB && I.srcProg.funcs.all linkFreeB &&
    I.srcProg.funcs.all (declSigB I.srcProg) && helperFreeB I.srcProg

theorem helperFreeB_sound {P : Clif.Program} (h : helperFreeB P = true) (op : DivOp) :
    P.func? (divHelper op) = none := by
  simp only [helperFreeB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  cases op
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem declSigB_sound {P : Clif.Program} {g : Clif.Function} (h : declSigB P g = true) :
    ∀ fn e, g.extern? fn = some e → ∀ h', P.func? e.name = some h' → h'.sig = e.sig := by
  intro fn e he h' hp
  simp only [declSigB, List.all_eq_true] at h
  obtain ⟨fn', hmem⟩ := E2E.LegalProgram.lookup_mem he
  have := h _ hmem
  simp only [hp, decide_eq_true_eq] at this
  exact this.symm

/-- **The domain of the whole-program refinement** of an input in the source domain whose
legalised program satisfies the linked system's facts (`LinkSys.Ok`'s `names`, `free`,
`declSig`, `indScope`), over a base environment with the `i128` contracts where needed. -/
theorem srcCtx {I : LinkInput} (hs : SrcScopeB I = true) {B : Clif.Env}
    {syms : String → Option Nat}
    (hnd : (I.prog.funcs.map (·.name)).Nodup) (hfree' : ∀ g ∈ I.prog.funcs, LinkFree g)
    (hdecl' : ∀ g ∈ I.prog.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h,
      I.prog.func? e.name = some h → e.sig = h.sig)
    (hind : ∀ g ∈ I.prog.funcs, ¬ IndFree g → IndScope I.prog B syms)
    (hlegal : (∃ f ∈ I.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B ∧ Opt.Legal.ExtLegal B ∧ Opt.Legal.EnvKeepsBounded B)
    (hsig : (∃ g ∈ I.prog.funcs, ¬ IndFree g) → ∀ n, B.sigOf n = none) :
    ProgCtx I.srcProg B syms := by
  simp only [SrcScopeB, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨⟨hok, hlf⟩, hds⟩, hhf⟩ := hs
  rw [LinkInput.prog_eq] at hnd hfree' hdecl' hind hsig
  have hnames : (legalProg I.srcProg).funcs.map (·.name) = I.srcProg.funcs.map (·.name) := by
    simp only [legalProg_funcs, List.map_map]
    exact List.map_congr_left fun f hf => (legalFacts (hok f hf)).name
  exact {
    ok := hok
    nd := by rw [← hnames]; exact hnd
    free := fun f hf => linkFreeB_sound (hlf f hf)
    free' := fun f hf => hfree' _ (List.mem_map_of_mem hf)
    decl := fun g hg => declSigB_sound (hds g hg)
    decl' := fun g hg fn e he h hp => by
      obtain ⟨fn', hmem⟩ := E2E.LegalProgram.lookup_mem he
      exact (hdecl' g hg e (List.mem_map.mpr ⟨(fn', e), hmem, rfl⟩) h hp).symm
    helpers := helperFreeB_sound hhf
    base := hlegal
    ind := fun ⟨g, hg, hnf⟩ => ⟨hind g hg hnf, hsig ⟨g, hg, hnf⟩⟩ }

end E2E.LinkCheck
