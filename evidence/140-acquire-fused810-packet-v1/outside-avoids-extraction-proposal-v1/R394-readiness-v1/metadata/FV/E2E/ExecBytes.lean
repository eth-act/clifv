import FV.E2E.Binary
import FV.E2E.ExecWords

/-! # The executable's own instruction words (L3, M9 item 1b)

`binary_correct_of_checks` (`FV/E2E/Binary.lean`) is about the **model** machine
`(sys I B).mach M f` run from `modelOf I f r`: the machine state `r` with the compiled image (the
compiled words, relocation fields zero) at the program's code addresses. That machine runs
`adrp`/`add`, `adrp`/`ldr` of the GOT, `bl`/`blr` and the TLSDESC sequence through hooks
(`ArmStepX`): the `adrp` writes the symbol's address, the second word of a pair does nothing, a
`bl` of a function of the program runs the callee's code as one step (`linkedCall`). Here the
theorem is moved to the **executable machine** `step I B file`, which runs the executable's own
words.

## The executable machine (`step`)

At the pc it looks up the kind of site there (`siteAt`: the kind, `siteOf`, of the program's
instruction there, from the compiled functions' layouts; only to decide which words are outside
code; two functions sharing code, a self-call alias, have the same kind at each word) and

* a `bl n` / `blr` whose callee is **outside the program**, the TLSDESC `adrp`, and its `ldr`
  (which in the model runs the rest of the sequence, `Hb.tls`): the base environment's hooks, as
  the model (code outside the program is given by its contract);
* every other word, **including** `adrp`+`add`, `adrp`+`ldr` (GOT), `bl`/`blr` to functions of
  the program: `realStep`, which fetches the 32-bit word **from the executable file**
  (`readN (Elf.loadMem file) 4 pc`, the read-only text), decodes it with the Arm model's decoder
  and executes it (`Arm.exec_inst`). The callee of a `bl` then runs in the same machine, and so
  on to its `ret`.

The `program` field of the state is not read by this machine.

## The simulation (`Sim`, `act_sim`)

`Sim I m e`: every register (incl. pc, flags, error) of the executable state `e` is the model
state `m`'s, every byte outside the relocated instruction bytes `RelocAt I` too (the program
field is not compared). The run of the model's activation of `g` at depth `M` is simulated:

* an instruction without relocation: the same decoded word on both sides (`ArtOk.plain`,
  `Insn.decode_encode`), one step each;
* a pair `adrp`; `add`/`ldr` at `P` (`RelocOk`, `PairOk`, words `ExecWords`): the two model steps
  against the two executable steps; after the first the register holds `page(T)` (resp.
  `page(G)`) in the executable and `T` in the model, after the second `T` in both
  (`adrp_add_val`, `adrp_ldr_addr`; for the GOT the slot's 8 bytes hold `T`);
* a `bl`/`blr` of a function `h` of the program at depth `M + 1`: the real `bl` (`blW_exec`) /
  `blr` (`blr_exec`) enters `h`'s code in the state `enterAt (art I h) m` (up to the program
  field), the callee's activation is simulated at depth `M` (induction on the depth) up to its
  first return (`RetOf`, `firstNat`), which is the model's `linkedCall`;
* outside calls and TLS: the same hook on both sides.

## What the simulation takes from the model run (`StepOk`, `RunOk`)

The model's ArmRefines does not expose its intermediate states, so the per-state facts the
lockstep needs are one explicit hypothesis, `RunOk`: `StepOk` at every state of the model's run
before its return (`Reach`, nested into the linked calls). `StepOk M g m` (`m` a state of an
activation of `g` at depth `M`): no error, the program field is `g`'s, the pc is at an
instruction of `g` (the site lookup, `siteAt`, giving its kind of site), and
* `cf`  (D1): a step that lands on the second word of a pair starts at its first word;
* `insn` / `call` / `tls` (D2): the instruction (resp. outside call, TLS hook) at `m` reads no
  relocated instruction byte (`Sim` before ⇒ `Sim` after);
* `got` (D4): at the `ldr` of a GOT pair the slot's 8 bytes are the file's, not relocated code;
* `blr`: the word the model reads at a `blr` to the program is the file's, and the callee's
  link-map address is its load address.
These hold of the M6 runs by construction (`RL.Good`, `StRel.code`, `StRel.gkeep`); proving them
there is the remaining work (docs/TO-PROVE.md L3).

## Trusted

The TLS local-exec sequence (`movz`/`movk`/`nop`/`nop`, checked by `BinCheck`, then `mrs
tpidr_el0`, `add`) is run through `Hb.tls`, as in the model: the Arm model has no system
registers.
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-! ## The executable machine -/

section Machine

variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- The executable's 32-bit word at `a` (its loaded image). -/
def fileWord (a : BitVec 64) : Option (BitVec 32) := readN (Elf.loadMem file) 4 a

/-- **One step of the processor on the executable's word at the pc**: fetch it from the file,
decode it, execute it; an error state stays put. -/
def realStep (s : Arm.ArmState) : Arm.ArmState :=
  match Arm.read_err s with
  | .None =>
    match (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst with
    | some a => Arm.exec_inst a s
    | none => Arm.w .ERR (.Other "no instruction word") s
  | _ => s

/-- **The kind of a site** of the program's code: what the executable machine does there. Code
shared by two functions of the program (a historical self-call alias `f__fvself` on `f`'s code)
has one kind at each word even where the functions' lines differ (`f`'s `bl f__fvself`,
`f__fvself`'s `bl f`: both a call of a function of the program, `progCall`). -/
inductive Site where
  /-- the processor on the file's word -/
  | real
  /-- a `bl` of a function of the program: the processor on the file's word -/
  | progCall
  /-- a `bl n` of code outside the program: the base environment's hook -/
  | extCall (n : String)
  /-- a `blr`: the processor when its target is a function of the program, else the hook -/
  | blr
  /-- the TLSDESC `adrp`: skipped, as in the model -/
  | tlsAdrp
  /-- the TLSDESC `ldr`: the TLS hook -/
  | tls (tmp : Reg) (n : String)

/-- The kind of the site of the instruction `i` of the program `P`. -/
def siteOf (P : Clif.Program) : Insn → Site
  | .bl n => if (P.func? n).isSome then .progCall else .extCall n
  | .blr _ => .blr
  | .adrpTlsDesc _ _ => .tlsAdrp
  | .ldrTlsDescLo12 tmp _ n => .tls tmp n
  | _ => .real

open Classical in
/-- **The kind of site at the address `a`**: that of the instruction there of some function of
the program whose code has one there (`siteOf`). -/
noncomputable def siteAt (a : BitVec 64) : Option Site :=
  if h : ∃ g ∈ (prog I).funcs, (insnAt (art I g).fa (art I g).base a).isSome then
    (insnAt (art I h.choose).fa (art I h.choose).base a).map (siteOf (prog I))
  else none

/-- The step at a site. -/
noncomputable def stepAt (site : Option Site) (s : Arm.ArmState) : Arm.ArmState :=
  match site with
  | some (.extCall n) => B.hooks.call (some n) s
  | some .blr =>
    if ((blrTarget s).bind (symCallee (sys I B).Xb (prog I))).isSome then realStep file s
    else B.hooks.call none s
  | some .tlsAdrp => Arm.w .PC (Arm.r .PC s + 4) s
  | some (.tls tmp n) => B.hooks.tls n tmp s
  | _ => realStep file s

/-- The step at an instruction of the program (`stepAt` of its kind of site, `stepAt_site`). -/
noncomputable def stepIns (site : Option Insn) (s : Arm.ArmState) : Arm.ArmState :=
  match site with
  | some (.bl n) => if ((prog I).func? n).isSome then realStep file s else B.hooks.call (some n) s
  | some (.blr _) =>
    if ((blrTarget s).bind (symCallee (sys I B).Xb (prog I))).isSome then realStep file s
    else B.hooks.call none s
  | some (.adrpTlsDesc _ _) => Arm.w .PC (Arm.r .PC s + 4) s
  | some (.ldrTlsDescLo12 tmp _ n) => B.hooks.tls n tmp s
  | _ => realStep file s

/-- **The executable machine**: the processor on the executable's words (`realStep`), but at
calls of code outside the program and at the TLS sequence, which run by the base environment's
hooks. -/
noncomputable def step (s : Arm.ArmState) : Arm.ArmState := stepAt I B file (siteAt I (Arm.r .PC s)) s

/-- **The executable machine state `e` simulates the model state `m`**: the same registers,
flags, pc and error, the same bytes but at relocated instruction bytes (the program field, which
neither machine's semantics of a word reads, is not compared). -/
def Sim (m e : Arm.ArmState) : Prop :=
  (∀ fld, Arm.r fld e = Arm.r fld m) ∧ ∀ a, ¬ RelocAt I a → e.mem a = m.mem a

/-- `a` is the second word of an `adrp` pair of `g` (its `add`/`ldr`). -/
def Second (g : Clif.Function) (a : BitVec 64) : Prop :=
  ∃ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) ∧
    a = wAt (art I g) (rl.offset + 4)

/-- The model's activation of `a` entered at `c` has returned in `t` (`RetOf` of the call). -/
def Returned (a : Art) (c t : Arm.ArmState) : Prop :=
  Arm.r .PC t = xreg 30 c ∧ Arm.r .ERR t = .None ∧ t.program = a.fb.program a.base ∧
    spv t = spv c

/-- The model's step at `s` (an activation of `g`) is a linked call of the function `h` of the
program. -/
def CallsAt (g : Clif.Function) (s : Arm.ArmState) (h : Clif.Function) : Prop :=
  (∃ n, insnAt (art I g).fa (progBase s) (Arm.r .PC s) = some (.bl n) ∧ (prog I).func? n = some h) ∨
  ((∃ x, insnAt (art I g).fa (progBase s) (Arm.r .PC s) = some (.blr x)) ∧
    (blrTarget s).bind (symCallee (sys I B).Xb (prog I)) = some h)

/-- **The states of the model's activation of `g` at depth `M` entered at `c`** before its
return, and of the activations it calls (`Reach M g c M' g' t`: `t` is a state of an activation
of `g'` at depth `M'`). -/
inductive Reach : Nat → Clif.Function → Arm.ArmState → Nat → Clif.Function → Arm.ArmState → Prop
  | act {M g c k} : (∀ j ≤ k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
      Reach M g c M g (runX ((sys I B).mach M g) k c)
  | nest {M g c k h M' g' t} :
      (∀ j ≤ k, ¬ Returned (art I g) c (runX ((sys I B).mach (M + 1) g) j c)) →
      CallsAt I B g (runX ((sys I B).mach (M + 1) g) k c) h →
      Reach M h (enterAt (art I h) (runX ((sys I B).mach (M + 1) g) k c)) M' g' t →
      Reach (M + 1) g c M' g' t

/-- **What the lockstep needs of a model state** `m` of an activation of `g` at depth `M` (see the
module doc). -/
structure StepOk (M : Nat) (g : Clif.Function) (m : Arm.ArmState) : Prop where
  err : Arm.r .ERR m = .None
  program : m.program = (art I g).fb.program (art I g).base
  /-- the pc is at an instruction of `g` (the site the executable machine looks up), not inside
  the TLS sequence past its `ldr` -/
  site : ∃ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i ∧
    siteAt I (Arm.r .PC m) = some (siteOf (prog I) i) ∧ (i.reloc? = none ∨ i.hooked = true)
  /-- D1: only the first word of a pair steps to its second -/
  cf : ∀ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) →
    Arm.r .PC ((sys I B).mach M g m) = wAt (art I g) (rl.offset + 4) →
    Arm.r .PC m = wAt (art I g) rl.offset
  /-- D2: an instruction without relocation reads no relocated instruction byte -/
  insn : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)
  /-- D2: nor does a call of code outside the program -/
  call : ∀ d e, ((∃ n, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.bl n) ∧
        (prog I).func? n = none ∧ d = some n) ∨
      ((∃ x, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x)) ∧
        (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) →
    Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e)
  /-- D2: nor the TLS sequence -/
  tls : ∀ tmp rn n e, insnAt (art I g).fa (art I g).base (Arm.r .PC m) =
      some (.ldrTlsDescLo12 tmp rn n) →
    Sim I m e → Sim I (B.hooks.tls n tmp m) (B.hooks.tls n tmp e)
  /-- D4: at the `ldr` of a GOT pair (`P`, register `rd`) loading the slot `G`, the slot holds
  the file's bytes, which are not relocated instruction bytes -/
  got : ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC m = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (pageOf G - pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    m.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0
  /-- a `blr` to the program: through a register (not `xzr`), the model reads the file's word,
  and the callee's link-map address is its load address -/
  blr : ∀ x h, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x) →
    (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = some h →
    x ≠ .xzr ∧ fileWord file (Arm.r .PC m) = some (Arm.read_mem_bytes 4 (Arm.r .PC m) m) ∧
    I.symAddr h.name 0 = (art I h).base
  /-- the instruction word at the pc is no relocated byte of another function -/
  plain : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.reloc? = none →
    ∀ k < 4, ¬ RelocAt I (Arm.r .PC m + BitVec.ofNat 64 k)

/-- **The hypothesis on the model's runs**: `StepOk` at every state of the activation of `f`
at depth `M` entered at `c` (and of the activations it calls) before its return. -/
def RunOk (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, Reach I B M f c M' g t → StepOk I B file M' g t

end Machine

/-! ## Basic facts -/

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem runX_succ' (f : Arm.ArmState → Arm.ArmState) (k : Nat) (s : Arm.ArmState) :
    runX f (k + 1) s = f (runX f k s) := by
  rw [runX_add f k 1]; rfl

theorem sim_w {m e : Arm.ArmState} (h : Sim I m e) (fld : Arm.StateField)
    (v : Arm.state_value fld) : Sim I (Arm.w fld v m) (Arm.w fld v e) := by
  refine ⟨fun f => ?_, fun a ha => ?_⟩
  · by_cases hf : f = fld
    · subst hf; rw [Arm.r_of_w_same, Arm.r_of_w_same]
    · rw [Arm.r_of_w_different hf, Arm.r_of_w_different hf]; exact h.1 f
  · rw [Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem]; exact h.2 a ha

theorem sim_set_program {m e : Arm.ArmState} (p : Arm.Program) (h : Sim I m e) :
    Sim I (Arm.set_program m p) e :=
  ⟨fun f => by rw [r_set_program]; exact h.1 f, fun a ha => by rw [mem_set_program]; exact h.2 a ha⟩

theorem insnAt_spec {fa : FnAsm} {base pc : BitVec 64} {i : Insn} (h : insnAt fa base pc = some i) :
    ∃ j t, fa.lines.toList[j]? = some (.ins i t) ∧
      base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) = pc := by
  unfold insnAt at h
  split at h
  · rename_i hex
    obtain ⟨t, h1, h2⟩ := Classical.choose_spec (Classical.choose_spec hex)
    cases h
    exact ⟨_, t, h1, h2⟩
  · cases h

theorem stepAt_real {site : Option Insn} (s : Arm.ArmState) (h1 : ∀ n, site ≠ some (.bl n))
    (h2 : ∀ x, site ≠ some (.blr x)) (h3 : ∀ a b, site ≠ some (.adrpTlsDesc a b))
    (h4 : ∀ a b c, site ≠ some (.ldrTlsDescLo12 a b c)) :
    stepIns I B file site s = realStep file s := by
  unfold stepIns
  split
  · exact absurd rfl (h1 _)
  · exact absurd rfl (h2 _)
  · exact absurd rfl (h3 _ _)
  · exact absurd rfl (h4 _ _ _)
  · rfl

theorem realStep_eq {s : Arm.ArmState} {a : Arm.ArmInst} (herr : Arm.r .ERR s = .None)
    (h : (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst = some a) :
    realStep file s = Arm.exec_inst a s := by
  have : Arm.read_err s = .None := herr
  simp only [realStep, this, h]

theorem returned_iff {a : Art} {s t : Arm.ArmState} : RetOf a s t ↔ Returned a (enterAt a s) t := by
  simp only [RetOf, Returned, x30_enterAt, spv_enterAt]

/-! ## Static facts of a compiled function in the executable -/

/-- The static facts of the function `g` of the program (layout, fit, binary check, address). -/
structure FnOk (I : LinkInput) (file : ByteArray) (g : Clif.Function) : Prop where
  layout : (art I g).fa.layout = .ok (art I g).fb
  fits : (art I g).base.toNat + 4 * (art I g).fb.words.size ≤ 2 ^ 64
  bin : ArtOk I file (art I g)
  base : (art I g).base = BitVec.ofNat 64 (I.baseOf g.name)

theorem fnOk {D : List Clif.DataObject} (hI : okB I = true) (hbin : BinOk I D file)
    {F : BitVec 64 → Prop} (hL : (LinkSys.ofInput I B F).Ok) {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  obtain ⟨-, -, -, -, hla, hb⟩ := (facts hI hg).pipe
  exact ⟨hla, hL.fits g hg, hbin.code _ (tab_mem (okB_names hI) hg), hb⟩

theorem wAt_inj {a : Art} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : wAt a x = wAt a y) : x = y := by
  simp only [wAt] at h
  have h' := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h)
  simp only [BitVec.toNat_ofNat] at h'
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'

theorem insnAt_of_line {g : Clif.Function} (hF : FnOk I file g) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins i t)) :
    insnAt (art I g).fa (art I g).base (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) =
      some i :=
  insnAt_line (by rw [layout_sum hF.layout]; have := hF.fits; omega) hj

theorem line_lt {g : Clif.Function} (hF : FnOk I file g) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins i t)) :
    lineOffset (art I g).fa.lines.toList j + 4 ≤ 4 * (art I g).fb.words.size := by
  have h1 := lineOffset_succ _ j _ hj
  have h2 := lineOffset_le_size (art I g).fa.lines.toList (j + 1)
  rw [layout_sum hF.layout] at h2
  simp only [Line.size] at h1
  omega

/-- The reloc of a line, and its offset. -/
theorem line_reloc {g : Clif.Function} (hF : FnOk I file g) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins i t))
    {ty : RelocType} {s : String} {ad : Int} (hi : i.reloc? = some (ty, s, ad)) :
    (⟨lineOffset (art I g).fa.lines.toList j, ty, s, ad⟩ : Reloc) ∈ (art I g).fb.relocs :=
  (FnAsm.layout_relocs hF.layout _).2 ⟨j, i, t, hj, hi, rfl⟩

/-- Two instructions at the same offset are the same line. -/
theorem line_unique {g : Clif.Function} {j j' : Nat} {i i' : Insn} {t t' : Option Clif.TrapCode}
    (hj : (art I g).fa.lines.toList[j]? = some (.ins i t))
    (hj' : (art I g).fa.lines.toList[j']? = some (.ins i' t'))
    (he : lineOffset (art I g).fa.lines.toList j = lineOffset (art I g).fa.lines.toList j') :
    i = i' := by
  obtain rfl := lineOffset_inj hj hj' he
  rw [hj] at hj'; cases hj'; rfl

/-- The executable's word of an instruction without relocation is the compiled word. -/
theorem fileWord_plain {g : Clif.Function} (hF : FnOk I file g) {lm : Std.HashMap Lbl Nat}
    (hm : labelOffsets (art I g).fa.lines = .ok lm) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins i t))
    (hr : i.reloc? = none) :
    ∃ w, i.encode ⟨lineOffset (art I g).fa.lines.toList j, (lm[·]?)⟩ = .ok w ∧
      fileWord file (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) = some w := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hF.layout hm hj rfl
  refine ⟨w, hw, ?_⟩
  have := hF.bin.plain _ w hk (fun r hr' ho => by
    obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hF.layout r).1 hr'
    have := line_unique hj hj' (by omega)
    subst this
    rw [hr] at hi'; cases hi')
  rw [show 4 * (lineOffset (art I g).fa.lines.toList j / 4) = lineOffset (art I g).fa.lines.toList j
    by omega] at this
  exact this

/-- The executable's word at a `blr` line decodes to the `blr` (a register, not `xzr`). -/
theorem blr_word {g : Clif.Function} (hF : FnOk I file g) {lm : Std.HashMap Lbl Nat}
    (hm : labelOffsets (art I g).fa.lines = .ok lm) {j : Nat} {x : Reg}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins (.blr x) t))
    (hx : x ≠ .xzr) :
    ∃ w rn, rn.toNat < 31 ∧
      fileWord file (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) = some w ∧
      Arm.decode_raw_inst w =
        some (.BR (.Uncond_branch_reg { opc := 1, op2 := 31, op3 := 0, Rn := rn, op4 := 0 })) := by
  obtain ⟨w, hw, hf⟩ := fileWord_plain hF hm hj rfl
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  cases x with
  | x n =>
    by_cases hn : n ≤ 30
    · rw [toArmInst_blr _ hn] at ha
      cases ha
      exact ⟨w, _, by simp; omega, hf, hd⟩
    · simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, Functor.map, Except.map, bind,
        Except.bind, throw, throwThe, MonadExceptOf.throw] at ha
  | xzr => exact absurd rfl hx
  | _ =>
    simp [Insn.toArmInst, Insn.armFields, Reg.encZR, Functor.map, Except.map, bind,
      Except.bind, throw, throwThe, MonadExceptOf.throw] at ha


theorem progBase_of {g : Clif.Function} (hF : FnOk I file g) {lm : Std.HashMap Lbl Nat}
    (hm : labelOffsets (art I g).fa.lines = .ok lm) {m : Arm.ArmState}
    (hp : m.program = (art I g).fb.program (art I g).base) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins i t)) :
    progBase m = (art I g).base := by
  obtain ⟨-, w, -, hk⟩ := FnAsm.layout_word hF.layout hm hj rfl
  refine progBase_eq (by rw [hp]; rfl) ?_
  intro h
  have : (art I g).fb.words.size = 0 := by simpa using congrArg List.length h
  simp [this] at hk

theorem wAt_add4 (a : Art) (o : Nat) : wAt a o + 4 = wAt a (o + 4) := by
  simp only [wAt]; rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

/-- The register of a compiled `adrp` whose word is `adrpW rdN 0`. -/
theorem adrp_reg {env : Env} {i : Insn} {rd : Reg} {rdN : Nat} (hrd : rdN < 31)
    (hi : (∃ n, i = .adrpGot rd n) ∨ ∃ n off, i = .adrp rd n off)
    (hw : i.encode env = .ok (adrpW rdN 0)) :
    rd.encZR.toOption.getD 31#5 = BitVec.ofNat 5 rdN := by
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  rw [(ExecWords.adrpW_exec hrd (by decide)).1] at hd
  cases hd
  rcases hi with ⟨n, rfl⟩ | ⟨n, off, rfl⟩ <;>
  · cases hv : rd.encZR with
    | error e =>
      simp [Insn.toArmInst, Insn.armFields, hv, Functor.map, Except.map, bind, Except.bind] at ha
    | ok v =>
      simp [Insn.toArmInst, Insn.armFields, hv, Functor.map, Except.map, bind, Except.bind, pure,
        Except.pure, ExecWords.adrpI, Arm.ArmInst.norm] at ha
      simp [Except.toOption, ha]

/-- The end of a pair: the model wrote `x` at the first word, the executable `y` then `x`. -/
theorem sim_pair_end {m e : Arm.ArmState} (h : Sim I m e) (v : BitVec 5) (x y : BitVec 64)
    (p q q' : BitVec 64) :
    Sim I (Arm.w .PC p (Arm.w .PC q (Arm.w (.GPR v) x m)))
      (Arm.w .PC p (Arm.w (.GPR v) x (Arm.w .PC q' (Arm.w (.GPR v) y e)))) := by
  rw [Arm.w_of_w_shadow, Arm.w_of_w_commute (show Arm.StateField.GPR v ≠ .PC by simp),
    Arm.w_of_w_shadow, Arm.w_of_w_shadow]
  exact sim_w (sim_w h _ _) _ _

/-- The step at an instruction's kind of site is the step at the instruction. -/
theorem stepAt_site (i : Insn) (s : Arm.ArmState) :
    stepAt I B file (some (siteOf (prog I) i)) s = stepIns I B file (some i) s := by
  cases i
  case bl n => by_cases h : ((prog I).func? n).isSome <;> simp [siteOf, stepAt, stepIns, h]
  all_goals rfl

theorem step_site {s : Arm.ArmState} {i : Insn}
    (h : siteAt I (Arm.r .PC s) = some (siteOf (prog I) i)) :
    step I B file s = stepIns I B file (some i) s := by
  unfold step; rw [h, stepAt_site]

theorem siteAt_of {M : Nat} {g : Clif.Function} {m : Arm.ArmState} (h : StepOk I B file M g m)
    {i : Insn} (hi : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) :
    siteAt I (Arm.r .PC m) = some (siteOf (prog I) i) := by
  obtain ⟨i', h1, h2, -⟩ := h.site
  rw [hi] at h1; cases h1; exact h2

/-- The first word of an `adrp` pair is a real site. -/
theorem siteOf_pairFirst {P : Clif.Program} {i : Insn} {ty : RelocType} {s : String} {a : Int}
    (h : i.reloc? = some (ty, s, a)) (ht : ty = .adrGotPage ∨ ty = .adrPrelPgHi21) :
    siteOf P i = .real := by
  cases i <;> simp only [Insn.reloc?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    first | rfl | (obtain ⟨rfl, -⟩ := h; rcases ht with h' | h' <;> cases h')

theorem pair_first_pc {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {rl : Reloc}
    (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21)
    {m e : Arm.ArmState} (hpc : Arm.r .PC m = wAt (art I g) rl.offset)
    (h0 : StepOk I B file M g m) (hs : Sim I m e) :
    Arm.r .PC ((sys I B).mach M g m) = Arm.r .PC (step I B file e) ∧
      Arm.r .ERR ((sys I B).mach M g m) = Arm.r .ERR (step I B file e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hF.layout rl).1 hrl
  have hR := hF.bin.reloc rl hrl
  have hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i := by
    rw [hpc, ← ho]; exact insnAt_of_line hF hj
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  -- the instruction and the checked words
  obtain ⟨rd, hrd⟩ : ∃ rd : Reg, (rl.type = .adrGotPage ∧ i = .adrpGot rd rl.sym ∧ rl.addend = 0) ∨
      (rl.type = .adrPrelPgHi21 ∧ i = .adrp rd rl.sym rl.addend) := by
    rcases ht with ht | ht <;> rw [ht] at hi <;> cases i <;> simp [Insn.reloc?] at hi
    · exact ⟨_, .inl ⟨ht, by rw [hi.1], hi.2.symm⟩⟩
    · exact ⟨_, .inr ⟨ht, by rw [hi.1, hi.2]⟩⟩
  have hR' : rl.offset % 4 = 0 ∧ ∃ rdN x0 x1, rdN < 31 ∧
      (art I g).fb.words[rl.offset / 4]? = some (adrpW rdN 0) ∧
      (∃ r' ∈ (art I g).fb.relocs, r'.offset = rl.offset + 4 ∧ r'.type = loOf rl.type) ∧
      fileWord file (wAt (art I g) rl.offset) = some x0 ∧
      fileWord file (wAt (art I g) (rl.offset + 4)) = some x1 ∧
      PairOk (Elf.loadMem file) (wAt (art I g) rl.offset).toNat
        (I.symAddr rl.sym rl.addend).toNat rdN (decide (rl.type = .adrGotPage)) x0 x1 := by
    unfold RelocOk at hR
    rcases ht with ht | ht <;> rw [ht] at hR ⊢ <;>
    · obtain ⟨h4, rdN, x0, x1, hlt, hw0, -, ⟨r', hr', hr'o, hr't, -⟩, hx0, hx1, hp⟩ := hR
      exact ⟨h4, rdN, x0, x1, hlt, hw0, ⟨r', hr', hr'o, hr't⟩, hx0, hx1, hp⟩
  obtain ⟨h4, rdN, x0, x1, hlt, hw0, ⟨r', hr', hr'o, hr't⟩, hx0, hx1, hp⟩ := hR'
  -- the register
  obtain ⟨-, w, hw, hk⟩ := FnAsm.layout_word hF.layout hm hj rfl
  rw [ho, hw0] at hk
  cases hk
  have hv : rd.encZR.toOption.getD 31#5 = BitVec.ofNat 5 rdN :=
    adrp_reg hlt (by
      rcases hrd with ⟨-, h, -⟩ | ⟨-, h⟩
      · exact .inl ⟨_, h⟩
      · exact .inr ⟨_, _, h⟩) hw
  -- the model's first step
  have hm1 : (sys I B).mach M g m = Arm.w .PC (Arm.r .PC m + 4)
      (Arm.w (.GPR (BitVec.ofNat 5 rdN)) (I.symAddr rl.sym rl.addend) m) := by
    show ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m = _
    rcases hrd with ⟨-, rfl, ha⟩ | ⟨-, rfl⟩
    · simp only [ArmStepX, hb, hins, ha]
      generalize rd.encZR.toOption.getD 31#5 = v at hv ⊢
      subst hv; rfl
    · simp only [ArmStepX, hb, hins]
      generalize rd.encZR.toOption.getD 31#5 = v at hv ⊢
      subst hv; rfl
  -- the executable's first step
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans h0.err
  have hP : (Arm.r .PC e).toNat = (wAt (art I g) rl.offset).toNat := by rw [hpe, hpc]
  have hsite0 : siteAt I (Arm.r .PC e) = some (siteOf (prog I) i) := by
    rw [hpe]; exact siteAt_of h0 hins
  have hstep0 : ∀ a, (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a →
      step I B file e = Arm.exec_inst a e := fun a ha => by
    rw [step_site hsite0, stepAt_real _ (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp), realStep_eq hee ha]
  rw [hm1]
  have hfin : ∀ dp : Int, BinCheck.inR (-2 ^ 20) (2 ^ 20) dp = true →
      fileWord file (wAt (art I g) rl.offset) = some (adrpW rdN dp) →
      Arm.r .PC (Arm.w .PC (Arm.r .PC m + 4)
          (Arm.w (.GPR (BitVec.ofNat 5 rdN)) (I.symAddr rl.sym rl.addend) m)) =
        Arm.r .PC (step I B file e) ∧
      Arm.r .ERR (Arm.w .PC (Arm.r .PC m + 4)
          (Arm.w (.GPR (BitVec.ofNat 5 rdN)) (I.symAddr rl.sym rl.addend) m)) =
        Arm.r .ERR (step I B file e) := by
    intro dp hr hx
    obtain ⟨ha0, hx0e⟩ := ExecWords.adrpW_exec hlt hr
    rw [hstep0 _ (by rw [hpe, hpc, hx, Option.bind_some]; exact ha0), hx0e]
    refine ⟨by rw [Arm.r_of_w_same, Arm.r_of_w_same, hpe], ?_⟩
    rw [Arm.r_of_w_different (show Arm.StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show Arm.StateField.ERR ≠ .GPR (BitVec.ofNat 5 rdN) by simp),
      Arm.r_of_w_different (show Arm.StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show Arm.StateField.ERR ≠ .GPR (BitVec.ofNat 5 rdN) by simp), hs.1]
  cases hp with
  | adrpAdd hr e0 e1 => subst e0; exact hfin _ hr hx0
  | adrpLdr G hgot h8 hr e0 e1 hG => subst e0; exact hfin _ hr hx0


/-- **A pair**: the model's two steps from the first word of an `adrp` pair, against the
executable's two steps on the resolved words. -/
theorem pair_step {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {rl : Reloc}
    (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21)
    {m e : Arm.ArmState} (hpc : Arm.r .PC m = wAt (art I g) rl.offset)
    (h0 : StepOk I B file M g m) (h1 : StepOk I B file M g ((sys I B).mach M g m))
    (hs : Sim I m e) :
    Sim I ((sys I B).mach M g ((sys I B).mach M g m)) (step I B file (step I B file e)) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hF.layout rl).1 hrl
  have hR := hF.bin.reloc rl hrl
  have hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i := by
    rw [hpc, ← ho]; exact insnAt_of_line hF hj
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  -- the instruction and the checked words
  obtain ⟨rd, hrd⟩ : ∃ rd : Reg, (rl.type = .adrGotPage ∧ i = .adrpGot rd rl.sym ∧ rl.addend = 0) ∨
      (rl.type = .adrPrelPgHi21 ∧ i = .adrp rd rl.sym rl.addend) := by
    rcases ht with ht | ht <;> rw [ht] at hi <;> cases i <;> simp [Insn.reloc?] at hi
    · exact ⟨_, .inl ⟨ht, by rw [hi.1], hi.2.symm⟩⟩
    · exact ⟨_, .inr ⟨ht, by rw [hi.1, hi.2]⟩⟩
  have hR' : rl.offset % 4 = 0 ∧ ∃ rdN x0 x1, rdN < 31 ∧
      (art I g).fb.words[rl.offset / 4]? = some (adrpW rdN 0) ∧
      (∃ r' ∈ (art I g).fb.relocs, r'.offset = rl.offset + 4 ∧ r'.type = loOf rl.type) ∧
      fileWord file (wAt (art I g) rl.offset) = some x0 ∧
      fileWord file (wAt (art I g) (rl.offset + 4)) = some x1 ∧
      PairOk (Elf.loadMem file) (wAt (art I g) rl.offset).toNat
        (I.symAddr rl.sym rl.addend).toNat rdN (decide (rl.type = .adrGotPage)) x0 x1 := by
    unfold RelocOk at hR
    rcases ht with ht | ht <;> rw [ht] at hR ⊢ <;>
    · obtain ⟨h4, rdN, x0, x1, hlt, hw0, -, ⟨r', hr', hr'o, hr't, -⟩, hx0, hx1, hp⟩ := hR
      exact ⟨h4, rdN, x0, x1, hlt, hw0, ⟨r', hr', hr'o, hr't⟩, hx0, hx1, hp⟩
  obtain ⟨h4, rdN, x0, x1, hlt, hw0, ⟨r', hr', hr'o, hr't⟩, hx0, hx1, hp⟩ := hR'
  -- the register
  obtain ⟨-, w, hw, hk⟩ := FnAsm.layout_word hF.layout hm hj rfl
  rw [ho, hw0] at hk
  cases hk
  have hv : rd.encZR.toOption.getD 31#5 = BitVec.ofNat 5 rdN :=
    adrp_reg hlt (by
      rcases hrd with ⟨-, h, -⟩ | ⟨-, h⟩
      · exact .inl ⟨_, h⟩
      · exact .inr ⟨_, _, h⟩) hw
  -- the model's first step
  have hm1 : (sys I B).mach M g m = Arm.w .PC (Arm.r .PC m + 4)
      (Arm.w (.GPR (BitVec.ofNat 5 rdN)) (I.symAddr rl.sym rl.addend) m) := by
    show ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m = _
    rcases hrd with ⟨-, rfl, ha⟩ | ⟨-, rfl⟩
    · simp only [ArmStepX, hb, hins, ha]
      generalize rd.encZR.toOption.getD 31#5 = v at hv ⊢
      subst hv; rfl
    · simp only [ArmStepX, hb, hins]
      generalize rd.encZR.toOption.getD 31#5 = v at hv ⊢
      subst hv; rfl
  -- the partner line
  obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have hpc1 : Arm.r .PC ((sys I B).mach M g m) = wAt (art I g) (rl.offset + 4) := by
    rw [hm1, Arm.r_of_w_same, hpc, wAt_add4]
  have hins' : insnAt (art I g).fa (art I g).base (Arm.r .PC ((sys I B).mach M g m)) = some i' := by
    rw [hpc1, ← hr'o, ← ho']; exact insnAt_of_line hF hj'
  have hi'' : (∃ a b c, i' = .ldrGotLo12 a b c) ∨ ∃ a b c d, i' = .addLo12 a b c d := by
    rcases ht with ht | ht <;> rw [hr't, ht] at hi' <;> cases i' <;> simp [Insn.reloc?, loOf] at hi'
    · exact .inl ⟨_, _, _, rfl⟩
    · exact .inr ⟨_, _, _, _, rfl⟩
  have hb1 : progBase ((sys I B).mach M g m) = (art I g).base := by
    rw [← hb, hm1]; simp only [progBase, Arm.w_program]
  have hm2 : (sys I B).mach M g ((sys I B).mach M g m) =
      Arm.w .PC (Arm.r .PC ((sys I B).mach M g m) + 4) ((sys I B).mach M g m) := by
    show ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa _ = _
    rcases hi'' with ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;> simp only [ArmStepX, hb1, hins']
  -- the executable's first step
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans h0.err
  have hP : (Arm.r .PC e).toNat = (wAt (art I g) rl.offset).toNat := by rw [hpe, hpc]
  have hsite0 : siteAt I (Arm.r .PC e) = some (siteOf (prog I) i) := by
    rw [hpe]; exact siteAt_of h0 hins
  have hsite1 : ∀ e1 : Arm.ArmState, Arm.r .PC e1 = Arm.r .PC ((sys I B).mach M g m) →
      siteAt I (Arm.r .PC e1) = some (siteOf (prog I) i') := fun e1 h => by
        rw [h]; exact siteAt_of h1 hins'
  have hstep0 : ∀ a, (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a →
      step I B file e = Arm.exec_inst a e := fun a ha => by
    rw [step_site hsite0, stepAt_real _ (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp), realStep_eq hee ha]
  have hstep1 : ∀ e1 a, Arm.r .PC e1 = Arm.r .PC ((sys I B).mach M g m) → Arm.r .ERR e1 = .None →
      (fileWord file (Arm.r .PC e1)).bind Arm.decode_raw_inst = some a →
      step I B file e1 = Arm.exec_inst a e1 := fun e1 a h he ha => by
    rw [step_site (hsite1 e1 h), stepAt_real _ (by rcases hi'' with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp)
      (by rcases hi'' with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp)
      (by rcases hi'' with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp)
      (by rcases hi'' with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp), realStep_eq he ha]
  have hT : BitVec.ofNat 64 (I.symAddr rl.sym rl.addend).toNat = I.symAddr rl.sym rl.addend := by
    simp
  rw [hm2, hm1]
  cases hp with
  | adrpAdd hr e0 e1 =>
    subst e0 e1
    obtain ⟨ha0, hx0e⟩ := ExecWords.adrpW_exec hlt hr
    have hs0 := hstep0 _ (by rw [hpe, hpc, hx0, Option.bind_some]; exact ha0)
    rw [hx0e, hP] at hs0
    obtain ⟨ha1, hx1e⟩ := ExecWords.addW_exec hlt hlt (Nat.mod_lt _ (by decide))
    rw [hs0, hstep1 _ _ (by rw [Arm.r_of_w_same, hpe, hpc1, ← wAt_add4, hpc])
      (by rw [Arm.r_of_w_different (show Arm.StateField.ERR ≠ .PC by simp),
        Arm.r_of_w_different (show Arm.StateField.ERR ≠ .GPR (BitVec.ofNat 5 rdN) by simp), hee])
      (by rw [Arm.r_of_w_same, hpe, hpc, wAt_add4, hx1, Option.bind_some]; exact ha1), hx1e,
      Arm.r_of_w_different (show Arm.StateField.GPR (BitVec.ofNat 5 rdN) ≠ .PC by simp),
      ]
    simp only [Arm.r_of_w_same, ExecWords.adrp_add_val, hT, hpe]
    exact sim_pair_end hs _ _ _ _ _ _
  | adrpLdr G hgot h8 hr e0 e1 hG =>
    subst e0 e1
    have hgt : rl.type = .adrGotPage := by simpa using hgot
    obtain ⟨ha0, hx0e⟩ := ExecWords.adrpW_exec hlt hr
    have hs0 := hstep0 _ (by rw [hpe, hpc, hx0, Option.bind_some]; exact ha0)
    rw [hx0e, hP] at hs0
    obtain ⟨ha1, hx1e⟩ := ExecWords.ldrW_exec (imm := G % 4096 / 8) hlt hlt (by omega)
    have hgot' := h1.got rl hrl hgt hpc1 rdN G hlt h8 hr hx0 hx1
    have hval : Arm.read_mem_bytes 8 (BitVec.ofNat 64 G) e =
        BitVec.ofNat 64 (I.symAddr rl.sym rl.addend).toNat := by
      obtain ⟨hrb, -⟩ := readN_bytes hG
      rw [← hrb]
      refine rmb_congr 8 _ fun k hk => ?_
      obtain ⟨hnr, hmem⟩ := hgot' k hk
      rw [hs.2 _ hnr, show m.mem _ = ((sys I B).mach M g m).mem _ by
        rw [hm1, Arm.ArmState.mem_w_eq_mem, Arm.ArmState.mem_w_eq_mem], hmem]
      simp [stOf, setMem]
    rw [hs0, hstep1 _ _ (by rw [Arm.r_of_w_same, hpe, hpc1, ← wAt_add4, hpc])
      (by rw [Arm.r_of_w_different (show Arm.StateField.ERR ≠ .PC by simp),
        Arm.r_of_w_different (show Arm.StateField.ERR ≠ .GPR (BitVec.ofNat 5 rdN) by simp), hee])
      (by rw [Arm.r_of_w_same, hpe, hpc, wAt_add4, hx1, Option.bind_some]; exact ha1), hx1e,
      Arm.r_of_w_different (show Arm.StateField.GPR (BitVec.ofNat 5 rdN) ≠ .PC by simp),
      ]
    simp only [Arm.r_of_w_same, ExecWords.adrp_ldr_addr h8, Arm.read_mem_bytes_of_w, hval, hT, hpe]
    exact sim_pair_end hs _ _ _ _ _ _


/-! ## One step of the model against the executable -/

/-- An instruction without relocation: the same word, one step each. -/
theorem plain_step {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {m e : Arm.ArmState}
    (h0 : StepOk I B file M g m) (hs : Sim I m e) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) (hh : i.hooked = false) :
    Sim I ((sys I B).mach M g m) (step I B file e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  have hr : i.reloc? = none := by
    obtain ⟨i', h1, -, h3⟩ := h0.site
    rw [hins] at h1; cases h1
    rcases h3 with h | h
    · exact h
    · rw [hh] at h; cases h
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := (sys I B).Xb) (H := (sys I B).hooks M) hF.layout hm
    (by have := hF.fits; omega) hj hh h0.program hpc.symm h0.err
  obtain ⟨w, hw, hf⟩ := fileWord_plain hF hm hj hr
  have hd := Insn.decode_encode_of ha hw
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hfa : (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a := by
    rw [← hpc]; show (fileWord file (wAt _ _)).bind _ = _; rw [hf, Option.bind_some]; exact hd
  have hex : step I B file e = Arm.exec_inst a e := by
    rw [step_site (by rw [hpe]; exact siteAt_of h0 hins),
      stepAt_real _ (fun n h => by cases h; simp [Insn.hooked] at hh)
        (fun n h => by cases h; simp [Insn.hooked] at hh)
        (fun _ _ h => by cases h; simp [Insn.hooked] at hh)
        (fun _ _ _ h => by cases h; simp [Insn.hooked] at hh),
      realStep_eq ((hs.1 .ERR).trans h0.err) (by rw [hpe]; exact hfa)]
  show Sim I (ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m) _
  rw [hstep, hex]
  exact h0.insn i hins hh a hfa e hs

theorem hooks_tls (L : LinkSys) (M : Nat) : (L.hooks M).tls = L.Hb.tls := by
  cases M <;> rfl

/-- The executable's `blr` target is the model's. -/
theorem blrTarget_sim {m e : Arm.ArmState} (hs : Sim I m e)
    (hpl : ∀ k < 4, ¬ RelocAt I (Arm.r .PC m + BitVec.ofNat 64 k)) : blrTarget e = blrTarget m := by
  have hw : Arm.read_mem_bytes 4 (Arm.r .PC e) e = Arm.read_mem_bytes 4 (Arm.r .PC m) m := by
    rw [hs.1 .PC]; exact rmb_congr 4 _ fun k hk => hs.2 _ (hpl k hk)
  unfold blrTarget
  rw [hw]
  split <;> simp [hs.1]

/-- The steps at a call of outside code and at the TLS sequence: the same hook. -/
theorem hook_step {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {m e : Arm.ArmState}
    (h0 : StepOk I B file M g m) (hs : Sim I m e) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i)
    (hk : (∃ n, i = .bl n ∧ (prog I).func? n = none) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none) ∨
      (∃ a b, i = .adrpTlsDesc a b) ∨ ∃ a b c, i = .ldrTlsDescLo12 a b c) :
    Sim I ((sys I B).mach M g m) (step I B file e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hse : step I B file e = stepIns I B file (some i) e :=
    step_site (by rw [hpe]; exact siteAt_of h0 hins)
  show Sim I (ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m) _
  rw [hse]
  rcases hk with ⟨n, rfl, hn⟩ | ⟨x, rfl, hn⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
  · simp only [ArmStepX, hb, hins, LinkSys.hooks_call, LinkSys.callHook, stepIns]
    rw [show (sys I B).P.func? n = none from hn, show (prog I).func? n = none from hn]
    exact h0.call _ e (.inl ⟨n, hins, hn, rfl⟩) hs
  · have hpl := h0.plain _ hins rfl
    simp only [ArmStepX, hb, hins, LinkSys.hooks_call, LinkSys.callHook, stepIns,
      blrTarget_sim hs hpl]
    rw [show ((blrTarget m).bind (symCallee (sys I B).Xb (sys I B).P)) = none from hn,
      show ((blrTarget m).bind (symCallee (sys I B).Xb (prog I))) = none from hn]
    exact h0.call _ e (.inr ⟨⟨x, hins⟩, hn, rfl⟩) hs
  · simp only [ArmStepX, hb, hins, stepIns, hpe]
    exact sim_w hs _ _
  · simp only [ArmStepX, hb, hins, stepIns, hooks_tls]
    exact h0.tls a b c e hins hs

theorem add_ofInt_sub (x : BitVec 64) (N : Nat) :
    x + BitVec.ofInt 64 ((N : Int) - x.toNat) = BitVec.ofNat 64 N := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- **A `bl`/`blr` of a function `h` of the program**: the executable's word enters `h` in the
model's callee entry state (up to the program field). -/
theorem call_enter {M : Nat} {g h : Clif.Function} (hF : FnOk I file g) (hFh : FnOk I file h)
    {m e : Arm.ArmState} (h0 : StepOk I B file M g m) (hs : Sim I m e)
    (hc : CallsAt I B g m h) : Sim I (enterAt (art I h) m) (step I B file e) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨i0, hi0, -, -⟩ := h0.site
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hi0
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans h0.err
  have hen : ∀ T : BitVec 64, T = (art I h).base →
      Sim I (enterAt (art I h) m) (Arm.w .PC T (Arm.w (.GPR 30#5) (Arm.r .PC e + 4) e)) := by
    intro T hT
    rw [hT, hpe]
    exact sim_w (sim_w (sim_set_program _ hs) _ _) _ _
  simp only [CallsAt, hb] at hc
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
  · -- `bl`: the resolved `blW` of `R_AARCH64_CALL26`
    rw [hins] at hi0; cases hi0
    have hrl := line_reloc hF hj (show (Insn.bl n).reloc? = some (.call26, n, 0) from rfl)
    have hR := hF.bin.reloc _ hrl
    simp only [RelocOk] at hR
    obtain ⟨-, -, hrange, hword⟩ := hR
    obtain ⟨hd, hx⟩ := ExecWords.blW_exec hrange
    have hst : step I B file e = Arm.exec_inst (ExecWords.blI ((I.baseOf n : Int) -
        (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)).toNat)) e := by
      rw [step_site (by rw [hpe]; exact siteAt_of h0 hins)]
      simp only [stepIns, hn, Option.isSome_some, ↓reduceIte]
      exact realStep_eq hee (by rw [hpe, ← hpc]; show (readN _ 4 (wAt _ _)).bind _ = _; rw [hword, Option.bind_some]; exact hd)
    rw [hst, hx]
    refine hen _ ?_
    rw [hpe, ← hpc, show (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j) =
      wAt (art I g) (lineOffset (art I g).fa.lines.toList j) from rfl, add_ofInt_sub,
      hFh.base, (Clif.Program.func?_some hn).2]
  · -- `blr`: the register holds the callee's address
    rw [hins] at hi0; cases hi0
    obtain ⟨hx, hfw, hsym⟩ := h0.blr x h hins hcal
    obtain ⟨w, rn, hrn, hw, hdw⟩ := blr_word hF hm hj hx
    rw [show wAt (art I g) (lineOffset (art I g).fa.lines.toList j) = Arm.r .PC m from hpc] at hw
    rw [hw, Option.some.injEq] at hfw
    have htgt : blrTarget m = some (Arm.r (.GPR rn) m) := by
      unfold blrTarget; rw [← hfw, hdw]
    rw [htgt] at hcal
    have hcal' := List.find?_some hcal
    simp only [beq_iff_eq] at hcal'
    have hst : step I B file e = Arm.exec_inst
        (.BR (.Uncond_branch_reg { opc := 1, op2 := 31, op3 := 0, Rn := rn, op4 := 0 })) e := by
      rw [step_site (by rw [hpe]; exact siteAt_of h0 hins)]
      have hpl := h0.plain _ hins rfl
      simp only [stepIns, blrTarget_sim hs hpl, htgt]
      rw [show (Option.some (Arm.r (.GPR rn) m)).bind (symCallee (sys I B).Xb (prog I)) = some h
        from hcal]
      simp only [Option.isSome_some, ↓reduceIte]
      exact realStep_eq hee (by rw [hpe, hw, Option.bind_some]; exact hdw)
    rw [hst, ExecWords.blr_exec rn hrn]
    refine hen _ ?_
    rw [hs.1, ← hsym]
    exact hcal'.symm

/-! ## Static control-flow facts -/

/-- The facts of `RelocOk` for the page relocation of a pair that the control-flow lemmas use. -/
theorem pair_facts {g : Clif.Function} (hF : FnOk I file g) {rl : Reloc}
    (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) :
    rl.offset % 4 = 0 ∧ rl.offset + 4 < 4 * (art I g).fb.words.size ∧
      ∃ r' ∈ (art I g).fb.relocs, r'.offset = rl.offset + 4 ∧ r'.type = loOf rl.type := by
  have hR := hF.bin.reloc rl hrl
  unfold RelocOk at hR
  rcases ht with ht | ht <;> rw [ht] at hR ⊢ <;>
  · obtain ⟨h4, rdN, x0, x1, -, -, hw1, ⟨r', hr', hr'o, hr't, -⟩, -⟩ := hR
    have := (Array.getElem?_eq_some_iff.1 hw1).1
    exact ⟨h4, by omega, r', hr', hr'o, hr't⟩

/-- The entry of a function is no second word of a pair. -/
theorem not_second_base {g : Clif.Function} (hF : FnOk I file g) :
    ¬ Second I g (art I g).base := by
  rintro ⟨rl, hrl, ht, he⟩
  obtain ⟨-, hlt, -⟩ := pair_facts hF hrl ht
  have hfit := hF.fits
  have h0 : wAt (art I g) 0 = wAt (art I g) (rl.offset + 4) := by
    rw [← he]; simp [wAt]
  have := wAt_inj (by omega) (by omega) h0
  omega

/-- The first word of a pair is no second word. -/
theorem first_not_second {g : Clif.Function} (hF : FnOk I file g) {rl : Reloc}
    (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) :
    ¬ Second I g (wAt (art I g) rl.offset) := by
  rintro ⟨rl2, hrl2, ht2, he⟩
  obtain ⟨-, hlt, -⟩ := pair_facts hF hrl ht
  obtain ⟨-, hlt2, r', hr', hr'o, hr't⟩ := pair_facts hF hrl2 ht2
  have hfit := hF.fits
  have hoff := wAt_inj (by omega) (by omega) he
  obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hF.layout rl).1 hrl
  obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have := line_unique hj hj' (by omega)
  subst this
  rw [hi] at hi'
  have := congrArg (fun x => x.map Prod.fst) hi'
  simp only [Option.map_some] at this
  injection this with e
  rw [hr't] at e
  rcases ht with h | h <;> rcases ht2 with h2 | h2 <;> rw [h, h2] at e <;> cases e

/-- An `add`/`ldr` of a pair is at a second word. -/
theorem second_of_lo12 {g : Clif.Function} (hF : FnOk I file g) {pc : BitVec 64} {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base pc = some i)
    (hk : (∃ a b c, i = .ldrGotLo12 a b c) ∨ ∃ a b c d, i = .addLo12 a b c d) :
    Second I g pc := by
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  obtain ⟨ty, s, ad, hr, hty⟩ : ∃ ty s ad, i.reloc? = some (ty, s, ad) ∧
      (ty = .ld64GotLo12Nc ∨ ty = .addAbsLo12Nc) := by
    rcases hk with ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · exact ⟨_, _, _, rfl, .inl rfl⟩
    · exact ⟨_, _, _, rfl, .inr rfl⟩
  have hR := hF.bin.reloc _ (line_reloc hF hj hr)
  unfold RelocOk at hR
  rcases hty with rfl | rfl <;>
  · obtain ⟨-, r', hr', ho, ht⟩ := hR
    exact ⟨r', hr', ht, by rw [← hpc]; show _ = wAt _ _; rw [ho]; rfl⟩

/-- The model's step at the first word of a pair lands on its second word. -/
theorem adrp_lands {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {m : Arm.ArmState}
    (h0 : StepOk I B file M g m) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i)
    (hk : (∃ a b, i = .adrpGot a b) ∨ ∃ a b c, i = .adrp a b c) :
    Second I g (Arm.r .PC ((sys I B).mach M g m)) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  obtain ⟨ty, s, ad, hr, hty⟩ : ∃ ty s ad, i.reloc? = some (ty, s, ad) ∧
      (ty = .adrGotPage ∨ ty = .adrPrelPgHi21) := by
    rcases hk with ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
    · exact ⟨_, _, _, rfl, .inl rfl⟩
    · exact ⟨_, _, _, rfl, .inr rfl⟩
  refine ⟨_, line_reloc hF hj hr, hty, ?_⟩
  show _ = wAt _ _
  rw [← wAt_add4, show wAt (art I g) (lineOffset (art I g).fa.lines.toList j) = Arm.r .PC m from hpc]
  show Arm.r .PC (ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m) = _
  rcases hk with ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp only [ArmStepX, hb, hins, Arm.r_of_w_same]

/-- The model's step at a call of a function `h` of the program: the linked call (depth `M + 1`),
an error (depth `0`). -/
theorem mach_call {M : Nat} {g h : Clif.Function} {m : Arm.ArmState} (hc : CallsAt I B g m h) :
    (sys I B).mach M g m = (sys I B).pcall M h m := by
  show ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m = _
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
  · simp only [ArmStepX, hins, LinkSys.hooks_call, LinkSys.callHook]
    rw [show (sys I B).P.func? n = some h from hn]
  · simp only [ArmStepX, hins, LinkSys.hooks_call, LinkSys.callHook]
    rw [show (blrTarget m).bind (symCallee (sys I B).Xb (sys I B).P) = some h from hcal]

theorem callee_mem {g h : Clif.Function} {m : Arm.ArmState} (hc : CallsAt I B g m h) :
    h ∈ (prog I).funcs := by
  rcases hc with ⟨n, -, hn⟩ | ⟨-, hcal⟩
  · exact (Clif.Program.func?_some hn).1
  · obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 hcal
    exact List.mem_of_find?_eq_some ha


/-- The return address of a call of `h` (the word after the `bl`/`blr`) is no second word of a
pair of `h` reached in `h`'s activation: its first word would be the call's word. -/
theorem ret_not_second (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M M' : Nat}
    {g h : Clif.Function} (hg : g ∈ (prog I).funcs) (hh : h ∈ (prog I).funcs) {m : Arm.ArmState}
    (hok0 : StepOk I B file M g m) (hc : CallsAt I B g m h)
    (hrun' : RunOk I B file M' h (enterAt (art I h) m)) {N : Nat}
    (hN : RetOf (art I h) m (runX ((sys I B).mach M' h) N (enterAt (art I h) m)))
    (hmin : ∀ j < N, ¬ RetOf (art I h) m (runX ((sys I B).mach M' h) j (enterAt (art I h) m))) :
    ¬ Second I h (Arm.r .PC (runX ((sys I B).mach M' h) N (enterAt (art I h) m))) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hFh := hF h hh
  cases N with
  | zero => exact not_second_base hFh ⟨rl, hrl, ht, (pc_enterAt (art I h) m).symm.trans he⟩
  | succ N1 =>
  have hokc := hrun' _ _ _ (Reach.act (k := N1) fun j hj => fun hr => hmin j (by omega) (returned_iff.2 hr))
  have hpc1 := hokc.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M' h) N1]; exact he)
  -- the first word's instruction
  obtain ⟨j, i1, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFh.layout rl).1 hrl
  have hins1 : insnAt (art I h).fa (art I h).base (wAt (art I h) rl.offset) = some i1 := by
    rw [← ho]; exact insnAt_of_line hFh hj
  have hs1 : siteAt I (wAt (art I h) rl.offset) = some (siteOf (prog I) i1) := by
    rw [← hpc1] at hins1 ⊢; exact siteAt_of hokc hins1
  -- the call's word is there
  have hpcm : Arm.r .PC m = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC m + 4 = wAt (art I h) rl.offset + 4 := by rw [← hN.1, he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨i0, hi0, hs0, -⟩ := hok0.site
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hi0
  have hb := progBase_of (hF g hg) hm hok0.program hj0
  simp only [CallsAt, hb] at hc
  rw [hpcm, hs1, siteOf_pairFirst hi ht] at hs0
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩ <;> rw [hins] at hi0 <;> cases hi0
  · simp [siteOf, hn] at hs0
  · simp [siteOf] at hs0

end Lemmas

/-! ## The simulation -/

/-- **The simulation of the model's activations at depth `M`** by the executable machine: from
related entry states, every state of the activation before its return that is not a pair's
second word is simulated by a state of the executable's run. -/
def ActSim (I : LinkInput) (B : BaseEnv) (file : ByteArray) (M : Nat) : Prop :=
  ∀ g c e, g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → Sim I c e → RunOk I B file M g c →
    ∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I B).mach M g) k c)) →
    ∃ k', Sim I (runX ((sys I B).mach M g) k c) (runX (step I B file) k' e)

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem junk_contra {M : Nat} {g : Clif.Function} {c : Arm.ArmState} (hrun : RunOk I B file M g c)
    {k : Nat} (hret : ∀ j < k + 1, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c))
    (hj : runX ((sys I B).mach M g) (k + 1) c = junkAt (runX ((sys I B).mach M g) k c)) : False := by
  have herr : Arm.r .ERR (runX ((sys I B).mach M g) (k + 1) c) ≠ .None := by
    rw [hj]; simp [junkAt, Arm.r_of_w_same]
  have hok := hrun _ _ _ (Reach.act (k := k + 1) fun j hj' => by
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact hret j h
    · obtain rfl : j = k + 1 := by omega
      exact fun hr => herr hr.2.1)
  exact herr hok.err

theorem act_core (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (M : Nat)
    (hcall : ∀ M', M = M' + 1 → ActSim I B file M') : ActSim I B file M := by
  intro g c e hg hpc hsim hrun k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hret hsec
  have hFg := hF g hg
  have hok : ∀ j, (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j' c)) →
      StepOk I B file M g (runX ((sys I B).mach M g) j c) := fun j hj =>
    hrun _ _ _ (Reach.act hj)
  cases k with
  | zero => exact ⟨0, hsim⟩
  | succ k0 =>
  have hok0 : StepOk I B file M g (runX ((sys I B).mach M g) k0 c) :=
    hok k0 fun j hj => hret j (by omega)
  rw [runX_succ'] at hsec ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I B).mach M g) k0 c))
  · -- the second word of a pair: two steps from its first word
    obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    have hok1 : StepOk I B file M g (runX ((sys I B).mach M g) k1 c) :=
      hok k1 fun j hj => hret j (by omega)
    have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact he)
    obtain ⟨k', hk'⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact first_not_second hFg hrl ht)
    refine ⟨k' + 2, ?_⟩
    rw [runX_succ', runX_add (step I B file) k' 2]
    exact pair_step hFg hrl ht hpc1 hok1
      (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact hok0) hk'
  · obtain ⟨k', hk'⟩ := ih k0 (by omega) (fun j hj => hret j (by omega)) hs
    obtain ⟨i, hins, -, -⟩ := hok0.site
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
    have hb := progBase_of hFg hm hok0.program hj0
    -- a call of a function of the program
    have hprog : ∀ h, CallsAt I B g (runX ((sys I B).mach M g) k0 c) h →
        ∃ k'', Sim I ((sys I B).mach M g (runX ((sys I B).mach M g) k0 c))
          (runX (step I B file) k'' e) := by
      intro h hc
      have hh := callee_mem hc
      rw [mach_call hc]
      cases M with
      | zero =>
        exact (junk_contra hrun hret (by rw [runX_succ', mach_call hc]; rfl)).elim
      | succ M' =>
      simp only [LinkSys.pcall]
      have hent := call_enter hFg (hF h hh) hok0 hk' hc
      have hrun' : RunOk I B file M' h (enterAt (art I h) (runX ((sys I B).mach (M' + 1) g) k0 c)) :=
        fun M'' g' t hr => hrun _ _ _ (Reach.nest (fun j hj => hret j (by omega)) hc hr)
      unfold linkedCall
      split
      · rename_i hex
        obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
        obtain ⟨k2, hk2⟩ := hcall M' rfl h _ _ hh (pc_enterAt _ _) hent hrun' _
          (fun j hj hr => hmin j hj (returned_iff.2 hr))
          (ret_not_second hF hg hh hok0 hc hrun' hN hmin)
        exact ⟨k' + 1 + k2, by rw [runX_add, runX_add]; exact sim_set_program _ hk2⟩
      · exact (junk_contra hrun hret (by rw [runX_succ', mach_call hc]; simp only [LinkSys.pcall, linkedCall]; simp [‹¬ _›])).elim
    by_cases hhk : i.hooked = false
    · exact ⟨k' + 1, by rw [runX_succ']; exact plain_step hFg hok0 hk' hins hhk⟩
    · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
      case bl n =>
        cases hn : (prog I).func? n with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩)⟩
        | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
      case blr x =>
        cases hn : (blrTarget (runX ((sys I B).mach M g) k0 c)).bind (symCallee (sys I B).Xb (prog I)) with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩))⟩
        | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
      case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
      case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
      case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
      case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
      case adrpTlsDesc a b =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩)))⟩
      case ldrTlsDescLo12 a b d =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩)))⟩

end Core

/-- **The simulation at every depth.** -/
theorem act_sim {I : LinkInput} {B : BaseEnv} {file : ByteArray}
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) : ∀ M, ActSim I B file M
  | 0 => act_core hF 0 fun _ h => by cases h
  | M + 1 => act_core hF (M + 1) fun M' h => by
    obtain rfl : M = M' := Nat.succ.inj h
    exact act_sim hF M

/-! ## The theorem about the executable -/

/-- **What the executable machine's run does for a CLIF outcome**: `ArmRefines`, with the live
CLIF bytes compared outside the relocated instruction bytes `R` (code bytes). -/
def ExecRefines (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (R : BitVec 64 → Prop) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The model state of `r` is simulated by `r`. -/
theorem sim_modelOf {f : Clif.Function} {r : Arm.ArmState}
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a) : Sim I (modelOf I f r) r :=
  ⟨fun fld => (r_modelOf I f r fld).symm, fun a ha =>
    Classical.byContradiction fun hne => ha (hd a (Ne.symm hne))⟩

/-- Before the state where the model's run is (`ArmRet` or `TrapAt`: no error) the activation
has not returned: past its return the machine errors for ever. -/
theorem no_return {M : Nat} {f : Clif.Function} (hFf : FnOk I file f) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    {n : Nat} (herr : Arm.r .ERR (runX ((sys I B).mach M f) n c) = .None) :
    ∀ j < n, ¬ Returned (art I f) c (runX ((sys I B).mach M f) j c) := by
  intro j hj hr
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFf.layout
  have := retStuck (X := (sys I B).Xb) (H := (sys I B).hooks M) hFf.layout hm hr.2.2.1
    (by rw [hr.1]; exact hra) (n - j - 1)
  change Arm.r .ERR (runX ((sys I B).mach M f) (n - j - 1 + 1) (runX ((sys I B).mach M f) j c)) ≠ .None
    at this
  rw [← runX_add, show j + (n - j - 1 + 1) = n by omega] at this
  exact this herr

/-- A second word of a pair is a code word of the function. -/
theorem second_code {f : Clif.Function} (hFf : FnOk I file f) {a : BitVec 64}
    (h : Second I f a) : ∃ k < (art I f).fb.words.size, a = (art I f).base + BitVec.ofNat 64 (4 * k) := by
  obtain ⟨rl, hrl, ht, rfl⟩ := h
  obtain ⟨h4, hlt, -⟩ := pair_facts hFf hrl ht
  exact ⟨(rl.offset + 4) / 4, by omega, by simp only [wAt]; congr 2; omega⟩

/-- **The model's outcome transfers to the executable machine**, given the per-state facts of
the model's run (`RunOk`). -/
theorem exec_of_model (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a)
    (hrun : RunOk I B file M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hsimN := act_sim (B := B) hF M f _ r hf hpc' hsim hrun
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, hret.pc]))
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v hv => ?_, fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · simp only [xreg]; rw [hk'.1]; exact hx j v hv
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (step I B file) k' r).mem =
        (runX (step I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_return (B := B) hFf hra' htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((sys I B).mach M f) n (modelOf I f r)))
    · -- a trap at a second word: one executable step after the first word
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (Reach.act (k := n1) fun j hj => hguard j (by omega))
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M f) n1]; exact he)
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact first_not_second hFf hrl ht)
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hok1 hk'
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hsimN n hguard hs
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial

end Transfer


/-- **The binary-level theorem about the executable's own words** (L3; `docs/contracts/e2e.md`,
"Binary level (M9)"): under the premises of `binary_correct_of_checks` and the per-state facts
of the model's run (`RunOk`), the **executable machine** (`step`: the processor on the
executable's words, outside calls and the TLS sequence by the base hooks) run from the machine
state `r` itself refines the whole-program CLIF run: it returns to the caller with the results,
the live CLIF bytes outside the relocated instruction bytes as the CLIF memory, or stops at the
trap site. -/
theorem binary_correct_exec_of_good {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hrun : RunOk I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  obtain ⟨h1, h2⟩ := binary_correct_of_checks hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
  have hL := okB_sound hI hB' fun _ h => .inr h
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  exact exec_of_model (fun g hg => fnOk hI hbin hL hg) hfm
    (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside h2 hrun h1

/-- **`binary_correct_exec_of_good` from the input condition** (no call cycle reachable from the
entry, as `binary_correct_of_checks_acyclic`). -/
theorem binary_correct_exec {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hrun : RunOk I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) :=
  binary_correct_exec_of_good hI hbin B hB ((StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩) hf M hX ho hr
    htr hrun

end E2E.ExecBytes
