import FV.E2E.LinkCheck

/-! # The code map check (L3, the executable machine)

`codeMapB`: the per-program check that the executable machine's site lookup
(`E2E.ExecBytes.siteAt`) and its `blr` agree with the model's: every function's link-map address is
its load address, or no `blr` of the program enters it; two functions' code ranges are disjoint,
or the two share their code with lines alike line by line (`cargo fv`'s self-call alias
`f__fvself` is a function of the program on `f`'s code). Decided here, on the compiled images
(`tabOf`), so that `link-check` evaluates it and the crate proofs decide it by `native_decide`;
its meaning is `E2E.ExecBytes.codeMap_sound`.
-/

namespace E2E.LinkCheck

open Backend

/-- The program of the compiled images `T`. -/
def progT (T : List (Clif.Function × Art)) : Clif.Program := { funcs := T.map (·.1) }

theorem progT_tabOf (R : Res) : progT (tabOf R) = progOf R := by
  simp [progT, tabOf, progOf, List.map_map, Function.comp_def]

/-- Two instructions of the program **alike**: the same, or calls (`bl`) of functions of the
program (the same kind of site, `E2E.ExecBytes.siteOf`, both relocated). -/
def insnAlikeB (P : Clif.Program) (i i' : Insn) : Bool :=
  decide (i = i') || match i, i' with
    | .bl n, .bl n' => (P.func? n).isSome && (P.func? n').isSome
    | _, _ => false

/-- Two lines alike: alike instructions, or two data words, or two labels. -/
def lineAlikeB (P : Clif.Program) : Line → Line → Bool
  | .ins i _, .ins i' _ => insnAlikeB P i i'
  | .word _ _, .word _ _ => true
  | .label _, .label _ => true
  | _, _ => false

/-- Two functions' lines alike line by line. -/
def linesAlikeB (P : Clif.Program) : List Line → List Line → Bool
  | [], [] => true
  | l :: L, l' :: L' => lineAlikeB P l l' && linesAlikeB P L L'
  | _, _ => false

/-- The calls through a register (`blr`) of the VCode `vc` are calls through the GOT entry
(`gotOf`) of a symbol other than `n`. -/
def blrGotB (vc : VCode) (n : String) : Bool :=
  vc.blocks.all fun vb => vb.insts.all fun i => match i with
    | .call info | .tryCall info _ => match info.dest with
      | .reg (.vreg t .int) => (gotOf vc t).any (· != n)
      | _ => true
    | _ => true

/-- **No `blr` of the program enters the function named `n`** (`LinkSys.BlrTo`): `n` has no
address in the CLIF image's symbol table (`syms`; so only a function declaring `n` may enter it
through a pointer), and every function of `T` declaring `n` calls through a register only
through the GOT entries of other symbols. -/
def noBlrB (I : LinkInput) (T : List (Clif.Function × Art)) (n : String) : Bool :=
  (I.syms.lookup n).isNone && T.all fun e =>
    !(e.1.externs.any fun x => x.2.name == n) || e.1.name == n || blrGotB e.2.vcp n

/-- **The code map** of a program's compiled images `T` (a per-program check, a premise of
`E2E.ExecBytes.binary_correct_exec_static`): every function's link-map address is its load address, or no
`blr` of the program enters it (`noBlrB`; `cargo fv`'s self-call alias `f__fvself` has a fresh
link-map address, and only `f` declares it, calling it by `bl`); the code ranges of two
functions are disjoint, or the two share their code (the same load address) with lines alike
line by line (`linesAlikeB`: the alias, `f`'s body whose self-call `bl f__fvself` is `bl f`).
So at every word of code the kind of site (`E2E.ExecBytes.siteOf`) is the same for every function there. -/
def codeMapB (I : LinkInput) (T : List (Clif.Function × Art)) : Bool :=
  T.all fun e => (I.symAddr e.1.name 0 == e.2.base || noBlrB I T e.1.name) &&
    T.all fun e' => e.1.name == e'.1.name ||
      decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat ∨
        e'.2.base.toNat + 4 * e'.2.fb.words.size ≤ e.2.base.toNat) ||
      (e.2.base == e'.2.base && linesAlikeB (progT T) e.2.fa.lines.toList e'.2.fa.lines.toList)

end E2E.LinkCheck
