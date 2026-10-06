import FV.E2E.ExecBytes

/-! # The static part of `RunOk` (L3)

`E2E.ExecBytes.binary_correct_exec` assumes `RunOk`: `StepOk` at every state of the model's run
before its return. Several of `StepOk`'s facts do not depend on the run; here they are proven for
every input, from the checks and one contract on the base environment, leaving the per-state
hypothesis `RunOkD` (`StepOkD`):

* `site`'s agreement of the site lookup (`siteAt_static`) and `plain` (`plain_static`): from the
  per-program code map check `codeMapB` (`codeMap_sound`: two functions' code ranges are
  disjoint) and the layout (a relocation is at its own instruction line);
* `blr`'s link-map address of a callee of the program (`codeMap_sound`: a function's link-map
  address is its load address);
* `call` and `tls`: the **outside-code contract `HooksSim`** on the base environment (next to
  `BaseOk`): the hooks for calls outside the program and for the TLS sequence do not read the
  program's relocated instruction bytes nor the machine's program field. `closedBase` meets it
  (`hooksSim_closed`).

`StepOkD` keeps what depends on the run: no error, the program field, the pc at an instruction of
the function (not past a TLSDESC `ldr`), D1 (`cf`), D2 (`insn`), D4 (`got`) and, at a `blr` to the
program, the register (not `xzr`) and the model's read of the `blr` word. Discharging it from the
M6 proof is TO-PROVE L3 (c). `binary_correct_exec_static` is `binary_correct_exec` under
`HooksSim` and `RunOkD`.
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-! ## The outside-code contract on the hooks -/

/-- **The base environment's hooks do not read the program's relocated instruction bytes nor the
program field** (`Sim` before gives `Sim` after): code outside the program, and the TLS sequence,
compute their effect from the registers and the bytes outside the relocated words. The contract
the executable machine adds to `BaseOk`. -/
structure HooksSim (I : LinkInput) (B : BaseEnv) : Prop where
  call : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e)
  tls : ∀ n tmp m e, Sim I m e → Sim I (B.hooks.tls n tmp m) (B.hooks.tls n tmp e)

/-- The closed base environment meets `HooksSim`. -/
theorem hooksSim_closed (I : LinkInput) : HooksSim I closedBase where
  call _ m e h := by
    show Sim I (Arm.w .PC (Arm.r .PC m + 4) m) (Arm.w .PC (Arm.r .PC e + 4) e)
    rw [h.1 .PC]; exact sim_w h _ _
  tls _ _ _ _ h := h

/-! ## The per-state hypothesis -/

section Defs

variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- **What the lockstep needs of a model state beyond the static facts** (`StepOk` without the
site lookup, `call`, `tls`, `plain` and the callee's link-map address). -/
structure StepOkD (M : Nat) (g : Clif.Function) (m : Arm.ArmState) : Prop where
  err : Arm.r .ERR m = .None
  program : m.program = (art I g).fb.program (art I g).base
  /-- the pc is at an instruction of `g`, not inside the TLS sequence past its `ldr` -/
  site : ∃ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i ∧
    (i.reloc? = none ∨ i.hooked = true)
  /-- D1 -/
  cf : ∀ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) →
    Arm.r .PC ((sys I B).mach M g m) = wAt (art I g) (rl.offset + 4) →
    Arm.r .PC m = wAt (art I g) rl.offset
  /-- D2 -/
  insn : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)
  /-- D4 -/
  got : ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC m = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (pageOf G - pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    m.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0
  /-- a `blr` to the program: through a register (not `xzr`), the model reads the file's word -/
  blr : ∀ x h, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x) →
    (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = some h →
    x ≠ .xzr ∧ fileWord file (Arm.r .PC m) = some (Arm.read_mem_bytes 4 (Arm.r .PC m) m)

/-- **The per-state hypothesis on the model's runs**: `StepOkD` at every state of the activation
of `f` at depth `M` entered at `c` (and of the activations it calls) before its return. -/
def RunOkD (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, Reach I B M f c M' g t → StepOkD I B file M' g t

end Defs

/-! ## The static facts -/

/-! ## The code map check -/

/-- **The code map** of a program's compiled images `T` (a per-program check, a premise of
`binary_correct_exec_static`): every function's link-map address is its load address, and the
code ranges of two functions are disjoint. (Not part of `okB`: a program with an alias of a
function, like `fv-demo`'s `…__fvself`, has two images on the same code, whose lines name
different callees, and another link-map address for the alias.) -/
def codeMapB (I : LinkInput) (T : List (Clif.Function × Art)) : Bool :=
  T.all fun e => I.symAddr e.1.name 0 == e.2.base &&
    T.all fun e' => e.1.name == e'.1.name ||
      decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat ∨
        e'.2.base.toNat + 4 * e'.2.fb.words.size ≤ e.2.base.toNat)

theorem codeMap_sound {I : LinkInput} (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    I.symAddr g.name 0 = (art I g).base ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      (art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat := by
  simp only [codeMapB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq] at hc
  have hn := okB_names hI
  have hgt := hc _ (tab_mem hn hg)
  exact ⟨hgt.1, fun g' hg' hne => (hgt.2 _ (tab_mem hn hg')).resolve_left hne⟩

section Static

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The entry of `R` named like `e0 ∈ R` is `e0` (distinct names). -/
theorem find_name {R : Res} : ((R.map (·.1)).map (·.name)).Nodup → ∀ {e0}, e0 ∈ R →
    R.find? (fun e => e.1.name == e0.1.name) = some e0 := by
  induction R with
  | nil => intro _ _ h; cases h
  | cons x R ih =>
    intro hn e0 h
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hne : x.1.name ≠ e0.1.name := fun he =>
        hn.1 (he ▸ List.mem_map_of_mem (List.mem_map_of_mem h'))
      simp [hne, ih hn.2 h']

/-- A relocated byte is in a relocated word of a function of the program. -/
theorem relocAt_inv (hI : okB I = true) {a : BitVec 64} (h : RelocAt I a) :
    ∃ g ∈ (prog I).funcs, ∃ rl ∈ (art I g).fb.relocs, ∃ i < 4, a = wAt (art I g) (rl.offset + i) := by
  obtain ⟨e, he, rl, hrl, i, hi, rfl⟩ := h
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have hart : art I e0.1 = getOk e0.2 := by
    simp only [art, artOf, find_name (okB_names hI) he0]
  exact ⟨e0.1, List.mem_map_of_mem he0, rl, by rw [hart]; exact hrl, i, hi, by rw [hart]⟩

/-- An instruction of `g` at `a`: its line, and `a` inside `g`'s code. -/
theorem insn_range {g : Clif.Function} (hF : FnOk I file g) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) :
    ∃ j t, (art I g).fa.lines.toList[j]? = some (.ins i t) ∧
      a.toNat = (art I g).base.toNat + lineOffset (art I g).fa.lines.toList j ∧
      lineOffset (art I g).fa.lines.toList j + 4 ≤ 4 * (art I g).fb.words.size := by
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hi
  have hl := line_lt hF hj
  have hfit := hF.fits
  refine ⟨j, t, hj, ?_, hl⟩
  rw [← hpc, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

theorem art_of_name {g h : Clif.Function} (he : g.name = h.name) : art I g = art I h := by
  simp only [art, artOf, he]

/-- **The site lookup finds the function's instruction** (no other function's code is there). -/
theorem siteAt_static (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) : siteAt I a = some i := by
  unfold siteAt
  split
  · rename_i hex
    have hs := hex.choose_spec
    generalize hex.choose = g0 at hs ⊢
    obtain ⟨hg0, hsome⟩ := hs
    suffices art I g0 = art I g by rw [this]; exact hi
    by_cases hn : g0.name = g.name
    · exact art_of_name hn
    · exfalso
      obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨j, -, -, ha, hl⟩ := insn_range (hF g hg) hi
      obtain ⟨j', -, -, ha', hl'⟩ := insn_range (hF g0 hg0) hi'
      have hd := (codeMap_sound hI hc hg0).2 g hg hn
      simp only [art] at ha ha' hl hl' hd
      omega
  · rename_i hne
    exact absurd ⟨g, hg, by rw [hi]; rfl⟩ hne

/-- **An instruction word without relocation is no relocated byte.** -/
theorem plain_static (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) (hr : i.reloc? = none) :
    ∀ k < 4, ¬ RelocAt I (a + BitVec.ofNat 64 k) := by
  intro k hk hR
  obtain ⟨j, t, hj, ha, hl⟩ := insn_range (hF g hg) hi
  obtain ⟨h, hh, rl, hrl, i', hi', he⟩ := relocAt_inv hI hR
  obtain ⟨j', i2, t2, hj', hri, ho⟩ := (FnAsm.layout_relocs (hF h hh).layout rl).1 hrl
  have hl' := line_lt (hF h hh) hj'
  have hfit := (hF h hh).fits
  have hfit' := (hF g hg).fits
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), wAt, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : rl.offset + i' < 2 ^ 64), Nat.mod_eq_of_lt (by omega)] at he'
  by_cases hn : h.name = g.name
  · have hart := art_of_name (I := I) hn
    rw [hart] at hj' he' ho hl'
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
    obtain ⟨h4, -⟩ := FnAsm.layout_word (hF g hg).layout hm hj rfl
    obtain ⟨h4', -⟩ := FnAsm.layout_word (hF g hg).layout hm hj' rfl
    have := line_unique hj hj' (by omega)
    subst this
    rw [hr] at hri; cases hri
  · have hd := (codeMap_sound hI hc hh).2 g hg hn
    simp only [art] at ha hl hl' he' hfit hfit' ho hd
    omega

/-- The states of the run are of functions of the program. -/
theorem reach_mem {M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat} {g : Clif.Function}
    {t : Arm.ArmState} (h : Reach I B M f c M' g t) (hf : f ∈ (prog I).funcs) :
    g ∈ (prog I).funcs := by
  induction h with
  | act _ => exact hf
  | nest _ hc _ ih => exact ih (callee_mem hc)

/-- **`StepOk` from `StepOkD`**, the checks and the hooks' contract. -/
theorem stepOk_of_d (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m : Arm.ArmState} (h : StepOkD I B file M g m) : StepOk I B file M g m where
  err := h.err
  program := h.program
  site := by
    obtain ⟨i, hi, hr⟩ := h.site
    exact ⟨i, hi, siteAt_static hI hc hF hg hi, hr⟩
  cf := h.cf
  insn := h.insn
  call d e _ hs := hH.call d m e hs
  tls tmp _ n e _ hs := hH.tls n tmp m e hs
  got := h.got
  blr x h' hx ht := by
    obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 ht
    have hh' : h' ∈ (prog I).funcs := List.mem_of_find?_eq_some ha
    exact ⟨(h.blr x h' hx ht).1, (h.blr x h' hx ht).2, (codeMap_sound hI hc hh').1⟩
  plain i hi hr := plain_static hI hc hF hg hi hr

/-- `StepOk` gives `StepOkD` (the per-state hypothesis is weaker). -/
theorem StepOk.d {M : Nat} {g : Clif.Function} {m : Arm.ArmState} (h : StepOk I B file M g m) :
    StepOkD I B file M g m :=
  ⟨h.err, h.program, let ⟨i, hi, _, hr⟩ := h.site; ⟨i, hi, hr⟩, h.cf, h.insn, h.got,
    fun x h' hx ht => ⟨(h.blr x h' hx ht).1, (h.blr x h' hx ht).2.1⟩⟩

theorem RunOk.d {M : Nat} {f : Clif.Function} {c : Arm.ArmState} (h : RunOk I B file M f c) :
    RunOkD I B file M f c :=
  fun M' g t hR => (h M' g t hR).d

theorem runOk_of_d (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {c : Arm.ArmState} (h : RunOkD I B file M f c) : RunOk I B file M f c :=
  fun M' g t hR => stepOk_of_d hI hc hF hH (reach_mem hR hf) (h M' g t hR)

end Static

/-- **`binary_correct_exec` with the static facts proven**: under the premises of
`binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim` and the per-state facts
`RunOkD` of the model's run, with the code map check `codeMapB`, the executable machine run from `r` refines the whole-program CLIF
run. -/
theorem binary_correct_exec_static {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs)
    (hrun : RunOkD I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hL := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  exact binary_correct_exec hI hbin B hB hf hc M hX ho hr htr
    (runOk_of_d hI hcm (fun g hg => fnOk hI hbin hL hg) hH (Clif.Program.func?_some hf).1 hrun)

end E2E.ExecBytes
