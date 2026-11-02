import FV.E2E.ExecBytes
import FV.E2E.CodeMap

/-! # The static part of `RunOk` (L3)

`E2E.ExecBytes.binary_correct_exec` assumes `RunOk`: `StepOk` at every state of the model's run
before its return. Several of `StepOk`'s facts do not depend on the run; here they are proven for
every input, from the checks and one contract on the base environment, leaving the per-state
hypothesis `RunOkD` (`StepOkD`):

* `site`'s agreement of the site lookup (`siteAt_static`) and `plain` (`plain_static`): from the
  per-program code map check `codeMapB` (`FV/E2E/CodeMap.lean`; `codeMap_sound`, `line_overlap`:
  two functions' overlapping words are alike lines, so one kind of site and one relocation
  status) and the layout (a relocation is at its own instruction line);
* `call` and `tls`: the **outside-code contract `HooksSim`** on the base environment (next to
  `BaseOk`): the hooks for calls outside the program and for the TLS sequence do not read the
  program's relocated instruction bytes nor the machine's program field. `closedBase` meets it
  (`hooksSim_closed`).

`StepOkD` keeps what depends on the run: no error, the program field, the pc at an instruction of
the function (not past a TLSDESC `ldr`), D1 (`cf`), D2 (`insn`), D4 (`got`) and, at a `blr` to the
program, the register (not `xzr`), the model's read of the `blr` word and the callee's link-map
address (from the M6 proof's `BlrAt` and `codeMapB`: `symAddr_of_blrTo`). Discharging it from the
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
  /-- a `blr` to the program: through a register (not `xzr`), the model reads the file's word,
  and the callee's link-map address is its load address -/
  blr : ∀ x h, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x) →
    (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = some h →
    x ≠ .xzr ∧ fileWord file (Arm.r .PC m) = some (Arm.read_mem_bytes 4 (Arm.r .PC m) m) ∧
    I.symAddr h.name 0 = (art I h).base

/-- **The per-state hypothesis on the model's runs**: `StepOkD` at every state of the activation
of `f` at depth `M` entered at `c` (and of the activations it calls) before its return. -/
def RunOkD (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, Reach I B M f c M' g t → StepOkD I B file M' g t

end Defs

/-! ## The static facts -/

/-! ## The code map check -/

theorem codeMap_sound {I : LinkInput} (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    (I.symAddr g.name 0 = (art I g).base ∨ noBlrB I (tabOf I.results) g.name = true) ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      ((art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat) ∨
      ((art I g).base = (art I g').base ∧
        linesAlikeB (prog I) (art I g).fa.lines.toList (art I g').fa.lines.toList = true) := by
  simp only [codeMapB, progT_tabOf, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at hc
  have hn := okB_names hI
  have hgt := hc _ (tab_mem hn hg)
  refine ⟨hgt.1, fun g' hg' hne => ?_⟩
  rcases hgt.2 _ (tab_mem hn hg') with (h | h) | h
  · exact absurd h hne
  · exact .inl h
  · exact .inr h

theorem insnAlikeB_site {P : Clif.Program} {i i' : Insn} (h : insnAlikeB P i i' = true) :
    siteOf P i = siteOf P i' := by
  simp only [insnAlikeB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · rfl
  · cases i <;> cases i' <;> simp_all [siteOf]

theorem insnAlikeB_reloc {P : Clif.Program} {i i' : Insn} (h : insnAlikeB P i i' = true)
    (hr : i.reloc? = none) : i'.reloc? = none := by
  simp only [insnAlikeB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · exact hr
  · cases i <;> cases i' <;> simp_all [Insn.reloc?]

theorem lineAlikeB_refl (P : Clif.Program) (l : Line) : lineAlikeB P l l = true := by
  cases l <;> simp [lineAlikeB, insnAlikeB]

theorem lineAlikeB_size {P : Clif.Program} {l l' : Line} (h : lineAlikeB P l l' = true) :
    l.size = l'.size := by
  cases l <;> cases l' <;> simp_all [lineAlikeB, Line.size]

theorem linesAlikeB_get {P : Clif.Program} :
    ∀ {L L' : List Line}, linesAlikeB P L L' = true → ∀ {j : Nat} {l : Line}, L[j]? = some l →
      ∃ l', L'[j]? = some l' ∧ lineAlikeB P l l' = true
  | [], _, _, _, _, hj => by simp at hj
  | _ :: _, [], h, _, _, _ => by simp [linesAlikeB] at h
  | l0 :: L, l0' :: L', h, j, l, hj => by
    simp only [linesAlikeB, Bool.and_eq_true] at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; exact ⟨l0', rfl, h.1⟩
    | succ j => simpa using linesAlikeB_get h.2 (by simpa using hj)

theorem linesAlikeB_offset {P : Clif.Program} :
    ∀ {L L' : List Line}, linesAlikeB P L L' = true → ∀ j, lineOffset L j = lineOffset L' j
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [linesAlikeB] at h
  | _ :: _, [], h, _ => by simp [linesAlikeB] at h
  | l0 :: L, l0' :: L', h, j => by
    simp only [linesAlikeB, Bool.and_eq_true] at h
    cases j with
    | zero => rfl
    | succ j =>
      have := linesAlikeB_offset h.2 j
      simp only [lineOffset, List.take_succ_cons, List.map_cons, List.sum_cons] at this ⊢
      rw [lineAlikeB_size h.1, this]

theorem blrGotB_sound {vc : VCode} {n : String} (h : blrGotB vc n = true) {info : CallInfo}
    (hs : vc.CallSite info) {t : Nat} (hd : info.dest = .reg (.vreg t .int)) :
    ∃ n', GotV vc t n' ∧ n' ≠ n := by
  obtain ⟨b, vb, k, hb, hi⟩ := hs
  have hvb := (array_all_iff _ _).1 h b vb hb
  have hg : (gotOf vc t).any (· != n) = true := by
    rcases hi with hi | ⟨ti, hi⟩ <;> simpa [hd] using (array_all_iff _ _).1 hvb k _ hi
  cases ho : gotOf vc t with
  | none => simp [ho] at hg
  | some n' =>
    simp only [ho, Option.any_some, bne_iff_ne, ne_eq] at hg
    exact ⟨n', gotOf_sound ho, hg⟩

/-- **The callee of a `blr` of the program has its link-map address at its load address**: a
`blr` of `g` through `t` may enter `h` (`BlrTo`) only if `h`'s link-map address is its load
address (`codeMapB`). -/
theorem symAddr_of_blrTo {I : LinkInput} {B : BaseEnv} (hI : okB I = true)
    (hc : codeMapB I (tabOf I.results) = true) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {info : CallInfo} {t : Nat} (hs : (art I g).vcp.CallSite info)
    (hd : info.dest = .reg (.vreg t .int)) (hb : (sys I B).BlrTo g t h) :
    I.symAddr h.name 0 = (art I h).base := by
  refine ((codeMap_sound hI hc hh).1).resolve_right fun hn => ?_
  simp only [noBlrB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hn
  obtain ⟨⟨hmay, -⟩, hgot⟩ := hb
  rcases hmay with hdecl | ⟨-, hsym, -⟩
  · rcases hn.2 _ (tab_mem (okB_names hI) hg) with hx | hx
    · obtain ⟨x, hx', he⟩ := List.mem_map.1 hdecl
      exact hx x hx' he
    · obtain ⟨n', hv, hn'⟩ := blrGotB_sound hx hs hd
      exact hn' (hgot n' hv)
  · exact hsym hn.1

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

/-- Lines of size 4 at the same offset are the same line. -/
theorem lineOffset_inj4 {L : List Line} {j j' : Nat} {ln ln' : Line} (hj : L[j]? = some ln)
    (hj' : L[j']? = some ln') (hs : ln.size = 4) (hs' : ln'.size = 4)
    (he : lineOffset L j = lineOffset L j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · have h1 := lineOffset_succ L j _ hj
    have h2 := lineOffset_mono L (show j + 1 ≤ j' by omega)
    omega
  · exact h
  · have h1 := lineOffset_succ L j' _ hj'
    have h2 := lineOffset_mono L (show j' + 1 ≤ j by omega)
    omega

/-- A line of `g` (not a label) is a word inside `g`'s code, at an offset that is a multiple
of 4. -/
theorem line_word {g : Clif.Function} (hF : FnOk I file g) {j : Nat} {l : Line}
    (hj : (art I g).fa.lines.toList[j]? = some l) (hl : l.isLabel = false) :
    l.size = 4 ∧ lineOffset (art I g).fa.lines.toList j % 4 = 0 ∧
      lineOffset (art I g).fa.lines.toList j + 4 ≤ 4 * (art I g).fb.words.size := by
  have hs : l.size = 4 := by cases l <;> simp_all [Line.size, Line.isLabel]
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  have h1 := lineOffset_succ _ j _ hj
  have h2 := lineOffset_le_size (art I g).fa.lines.toList (j + 1)
  rw [layout_sum hF.layout] at h2
  exact ⟨hs, (FnAsm.layout_word hF.layout hm hj hl).1, by omega⟩

/-- **Overlapping words of two functions are alike lines** (`codeMapB`): the same function's
same line, or the lines at the same offset of two functions sharing their code. -/
theorem line_overlap (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {j j' : Nat} {l l' : Line}
    (hj : (art I g).fa.lines.toList[j]? = some l) (hj' : (art I h).fa.lines.toList[j']? = some l')
    (hl : l.isLabel = false) (hl' : l'.isLabel = false) {k k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (he : (art I g).base.toNat + lineOffset (art I g).fa.lines.toList j + k =
      (art I h).base.toNat + lineOffset (art I h).fa.lines.toList j' + k') :
    lineAlikeB (prog I) l l' = true := by
  obtain ⟨hs, h4, hlt⟩ := line_word (hF g hg) hj hl
  obtain ⟨hs', h4', hlt'⟩ := line_word (hF h hh) hj' hl'
  by_cases hn : g.name = h.name
  · have hart := art_of_name (I := I) hn
    rw [← hart] at hj' he h4'
    obtain rfl := lineOffset_inj4 hj hj' hs hs' (by omega)
    rw [hj] at hj'; cases hj'
    exact lineAlikeB_refl _ _
  · rcases (codeMap_sound hI hc hg).2 h hh hn with hd | ⟨hb, ha⟩
    · exfalso
      have hfit := (hF g hg).fits
      have hfit' := (hF h hh).fits
      omega
    · rw [hb] at he
      have hoff := linesAlikeB_offset ha j
      obtain ⟨l'', hj'', hal⟩ := linesAlikeB_get ha hj
      have hs'' : l''.size = 4 := by rw [← lineAlikeB_size hal]; exact hs
      obtain rfl := lineOffset_inj4 hj'' hj' hs'' hs' (by omega)
      rw [hj''] at hj'; cases hj'
      exact hal

/-- **The site lookup finds the kind of site of the function's instruction** (the code of
another function there has an alike instruction). -/
theorem siteAt_static (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) :
    siteAt I a = some (siteOf (prog I) i) := by
  unfold siteAt
  split
  · rename_i hex
    have hs := hex.choose_spec
    generalize hex.choose = g0 at hs ⊢
    obtain ⟨hg0, hsome⟩ := hs
    obtain ⟨i0, hi0⟩ := Option.isSome_iff_exists.mp hsome
    rw [hi0, Option.map_some]
    obtain ⟨j, t, hj, ha, -⟩ := insn_range (hF g hg) hi
    obtain ⟨j0, t0, hj0, ha0, -⟩ := insn_range (hF g0 hg0) hi0
    have hal := line_overlap hI hc hF hg0 hg hj0 hj rfl rfl (k := 0) (k' := 0) (by omega)
      (by omega) (by omega)
    simp only [lineAlikeB] at hal
    rw [insnAlikeB_site hal]
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
  have hal := line_overlap hI hc hF hg hh hj hj' rfl rfl hk hi' (by rw [ho]; omega)
  simp only [lineAlikeB] at hal
  rw [insnAlikeB_reloc hal hr] at hri
  cases hri

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
  blr := h.blr
  plain i hi hr := plain_static hI hc hF hg hi hr

/-- `StepOk` gives `StepOkD` (the per-state hypothesis is weaker). -/
theorem StepOk.d {M : Nat} {g : Clif.Function} {m : Arm.ArmState} (h : StepOk I B file M g m) :
    StepOkD I B file M g m :=
  ⟨h.err, h.program, let ⟨i, hi, _, hr⟩ := h.site; ⟨i, hi, hr⟩, h.cf, h.insn, h.got,
    h.blr⟩

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
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hrun : RunOkD I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hL := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  exact binary_correct_exec hI hbin B hB hf hc M hX ho hr htr
    (runOk_of_d hI hcm (fun g hg => fnOk hI hbin hL hg) hH (Clif.Program.func?_some hf).1 hrun)

end E2E.ExecBytes
