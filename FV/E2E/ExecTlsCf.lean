import FV.E2E.ExecGoodRun
import FV.E2E.TlsLines

/-! # D1 of the TLS sequence from the M6 proof (T1)

The hook-free executable machine (`ExecTls.lean`) runs lld's local-exec words of a `tls_value`
(`movz`, `movk`, `nop`, `nop`, `mrs`, `add`) where the model runs its TLSDESC `adrp` (one step)
and its `ldr` (the TLS hook, one step to the end of the sequence). Between the two model states
the executable's register `x0` already holds the `movz` value, so the simulation needs, as for
the second word of an `adrp` pair, that a model step lands on the TLSDESC `ldr` only from its
`adrp` (`TlsCf`). This is D1 of the register-level proof: `RL.NextOk` excludes landing on a line
after a TLSDESC `adrp` other than from it (`Insn.pairFirst` includes `adrpTlsDesc`), and the
emitted lines keep the sequence whole (`emitFunc_tlsClosed`).

* `TlsSecond I g a`: `a` is the TLSDESC `ldr` word of a sequence of `g`;
* `TlsCf`, `RunTlsN`: D1 at a model state, at every `ReachN` state whose step ends without error;
* `runTlsN_of_good`: `RunTlsN` from the M6 proof's `RunGoodL`, for an activation whose return
  address is outside its code.
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

section Defs

variable (I : LinkInput) (B : BaseEnv)

/-- `a` is the TLSDESC `ldr` word of a TLS sequence of `g` (the word after its `adrp`). -/
def TlsSecond (g : Clif.Function) (a : BitVec 64) : Prop :=
  ∃ rl ∈ (art I g).fb.relocs, rl.type = .tlsDescAdrPage21 ∧ a = wAt (art I g) (rl.offset + 4)

/-- **D1 of the TLS sequence at the model state `m`** (an activation of `g` at depth `M`): a step
that lands on the TLSDESC `ldr` starts at its `adrp`. -/
def TlsCf (M : Nat) (g : Clif.Function) (m : Arm.ArmState) : Prop :=
  ∀ rl ∈ (art I g).fb.relocs, rl.type = .tlsDescAdrPage21 →
    Arm.r .PC ((sys I B).mach M g m) = wAt (art I g) (rl.offset + 4) →
    Arm.r .PC m = wAt (art I g) rl.offset

/-- `TlsCf` at the states of `ReachN` whose step ends without error. -/
def RunTlsN (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    TlsCf I B M' g t

end Defs

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The lines of a function of the program keep the TLS sequences whole. -/
theorem tlsClosed_art (hI : okB I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    TlsClosed (art I g).fa.lines.toList :=
  emitFunc_tlsClosed (facts hI hg).pipe.2.2.2.1

/-- The line of a TLSDESC page relocation: the sequence's `adrp` at line `j`, its `ldr` at
`j + 1` (four bytes on). -/
theorem tls_lines {g : Clif.Function} (hF : FnOk I file g) (hT : TlsClosed (art I g).fa.lines.toList)
    {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .tlsDescAdrPage21) :
    ∃ j t, (art I g).fa.lines.toList[j]? = some (.ins (.adrpTlsDesc (.x 0) rl.sym) t) ∧
      lineOffset (art I g).fa.lines.toList j = rl.offset ∧
      ∃ tmp, tmp ≠ .x 0 ∧
      (∃ t1, (art I g).fa.lines.toList[j + 1]? = some (.ins (.ldrTlsDescLo12 tmp (.x 0) rl.sym) t1)) ∧
      (∃ t2, (art I g).fa.lines.toList[j + 2]? = some (.ins (.addTlsDescLo12 (.x 0) (.x 0) rl.sym) t2)) ∧
      (∃ t3, (art I g).fa.lines.toList[j + 3]? = some (.ins (.blrTlsDesc tmp rl.sym) t3)) ∧
      (∃ t4, (art I g).fa.lines.toList[j + 4]? = some (.ins (.mrsTpidrEl0 tmp) t4)) ∧
      (∃ t5, (art I g).fa.lines.toList[j + 5]? =
        some (.ins (.aluRRR .add true (.x 0) (.x 0) tmp) t5)) := by
  obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hF.layout rl).1 hrl
  obtain ⟨rd, rfl⟩ : ∃ rd, i = .adrpTlsDesc rd rl.sym := by
    rw [ht] at hi
    cases i <;> simp [Insn.reloc?] at hi
    exact ⟨_, by rw [hi.1]⟩
  obtain ⟨rfl, hseq⟩ := hT j rd rl.sym t hj
  exact ⟨j, t, hj, ho, hseq⟩

/-- The offsets of a TLS sequence: word-aligned, its `ldr` inside the code. -/
theorem tls_facts {g : Clif.Function} (hF : FnOk I file g) (hT : TlsClosed (art I g).fa.lines.toList)
    {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs) (ht : rl.type = .tlsDescAdrPage21) :
    rl.offset % 4 = 0 ∧ rl.offset + 4 < 4 * (art I g).fb.words.size := by
  obtain ⟨j, t, hj, ho, tmp, -, ⟨t1, hj1⟩, -⟩ := tls_lines hF hT hrl ht
  have h1 := lineOffset_succ _ j _ hj
  have h2 := line_lt hF hj1
  simp only [Line.size] at h1
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨h4, -⟩ := FnAsm.layout_word hF.layout hm hj rfl
  exact ⟨by rw [← ho]; exact h4, by omega⟩

/-- The entry of a function is no TLSDESC `ldr` word. -/
theorem not_tlsSecond_base {g : Clif.Function} (hF : FnOk I file g)
    (hT : TlsClosed (art I g).fa.lines.toList) : ¬ TlsSecond I g (art I g).base := by
  rintro ⟨rl, hrl, ht, he⟩
  obtain ⟨-, hlt⟩ := tls_facts hF hT hrl ht
  have hfit := hF.fits
  have h0 : wAt (art I g) 0 = wAt (art I g) (rl.offset + 4) := by
    rw [← he]; simp [wAt]
  have := wAt_inj (by omega) (by omega) h0
  omega

/-- A TLSDESC `ldr` word is a code word of the function. -/
theorem tlsSecond_code {f : Clif.Function} (hFf : FnOk I file f)
    (hT : TlsClosed (art I f).fa.lines.toList) {a : BitVec 64} (h : TlsSecond I f a) :
    ∃ k < (art I f).fb.words.size, a = (art I f).base + BitVec.ofNat 64 (4 * k) := by
  obtain ⟨rl, hrl, ht, rfl⟩ := h
  obtain ⟨h4, hlt⟩ := tls_facts hFf hT hrl ht
  exact ⟨(rl.offset + 4) / 4, by omega, by simp only [wAt]; congr 2; omega⟩

/-- The top entry's return address, outside the code, is no TLSDESC `ldr` word. -/
theorem raNotTlsSecond_top {f : Clif.Function} (hF : FnOk I file f)
    (hT : TlsClosed (art I f).fa.lines.toList) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k)) :
    ¬ TlsSecond I f (xreg 30 c) := fun hs => by
  obtain ⟨k, hk, he⟩ := tlsSecond_code hF hT hs
  exact hra k hk he

/-- The TLSDESC `adrp` is a site of its own kind. -/
theorem siteOf_adrpTls (P : Clif.Program) (rd : Reg) (n : String) :
    siteOf P (.adrpTlsDesc rd n) = .tlsAdrp := rfl

/-- The return address of a callee entered at a call of the program is no TLSDESC `ldr` word of
the callee: the call's word would be the callee's TLSDESC `adrp`. -/
theorem raNotTlsSecond_enter (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    {u : Arm.ArmState} (hp : u.program = (art I g).fb.program (art I g).base)
    (hcall : CallsAt I B g u h) : ¬ TlsSecond I h (xreg 30 (enterAt (art I h) u)) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hh := callee_mem hcall
  rw [x30_enterAt] at he
  have hpcu : Arm.r .PC u = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC u + 4 = wAt (art I h) rl.offset + 4 := by rw [he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  have hins0 : ∃ i0, insnAt (art I g).fa (progBase u) (Arm.r .PC u) = some i0 ∧
      siteOf (prog I) i0 ≠ .tlsAdrp := by
    rcases hcall with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩
    · exact ⟨_, hins, by simp [siteOf, hn]⟩
    · exact ⟨_, hins, by simp [siteOf]⟩
  obtain ⟨i0, hi0, hr0⟩ := hins0
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hi0
  rw [progBase_of (hF g hg) hm hp hj0] at hi0
  have hs0 := siteAt_static hI hc hF hg hi0
  obtain ⟨j, t, hj, ho, -⟩ := tls_lines (hF h hh) (tlsClosed_art hI hh) hrl ht
  have hs1 := siteAt_static hI hc hF hh (insnAt_of_line (hF h hh) hj)
  rw [ho, ← hpcu, hs0, siteOf_adrpTls] at hs1
  exact hr0 (Option.some.inj hs1)

/-- **The states of `ReachN` are states of `ReachL`**, of an activation entered at an entry whose
return address is neither a pair's second word nor a TLSDESC `ldr` word. -/
theorem reachL_of_reachNT (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    {M' : Nat} {g : Clif.Function} {t : Arm.ArmState} (h : ReachN I B M f c M' g t) :
    f ∈ (prog I).funcs → (sys I B).RunGoodL M f c → ¬ Second I f (xreg 30 c) →
    ¬ TlsSecond I f (xreg 30 c) →
    ∃ c', (sys I B).ReachL M f c M' g c' t ∧ ¬ Second I g (xreg 30 c') ∧
      ¬ TlsSecond I g (xreg 30 c') := by
  induction h with
  | act hj => exact fun _ _ hs ht => ⟨_, .act hj, hs, ht⟩
  | nest hj hcall herr _ ih =>
    intro hf hrun _ _
    have hu := hrun _ _ _ _ (.act hj) (by rw [runX_succ'] at herr; exact herr)
    obtain ⟨X, K, G, gv, -, hG, -⟩ := hu
    unfold actGoodX at hG
    obtain ⟨c', hR', hs', ht'⟩ := ih (callee_mem hcall)
      (fun _ _ _ _ hr he => hrun _ _ _ _ (.nest hj hcall herr hr) he)
      (raNotSecond_enter hI hc hF hf hG.prog hcall)
      (raNotTlsSecond_enter hI hc hF hf hG.prog hcall)
    exact ⟨c', .nest hj hcall herr hR', hs', ht'⟩

/-- **`TlsCf` from the register-level per-state facts** (`RL.GoodX.next`). -/
theorem tlsCf_of_good (hI : okB I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState}
    (hgood : (sys I B).GoodAt M g c t) (hs : ¬ TlsSecond I g (xreg 30 c))
    (he : Arm.r .ERR ((sys I B).mach M g t) = .None) : TlsCf I B M g t := by
  obtain ⟨X, K, G, gv, heq, hG, -, -, -⟩ := hgood
  unfold actGoodX at hG
  have hFg := hF g hg
  have hfit := hFg.fits
  intro rl hrl ht hpcv
  have hn := hG.next
  have hstep : ArmStepX X ((sys I B).hooks M) ((sys I B).A g).fa t = (sys I B).mach M g t :=
    congrFun heq t
  simp only [RL.step] at hn
  rw [hstep] at hn
  rcases hn with h | h | h | ⟨j, hj, hpf⟩
  · exact absurd he h
  · exact absurd ⟨rl, hrl, ht, by rw [← h]; exact hpcv⟩ hs
  · have h2 : Arm.r .PC t + 4 = wAt (art I g) rl.offset + 4 := by
      rw [← h, hpcv, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  · exfalso
    obtain ⟨k', t', hy, ho, tmp, -, ⟨t1, hy1⟩, -⟩ := tls_lines hFg (tlsClosed_art hI hg) hrl ht
    have hyf : (Insn.adrpTlsDesc (.x 0) rl.sym).pairFirst = true := rfl
    obtain ⟨-, hlt⟩ := tls_facts hFg (tlsClosed_art hI hg) hrl ht
    -- the offsets
    have hoff : BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) =
        BitVec.ofNat 64 (rl.offset + 4) := by
      have h1 : (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList (j + 1)) =
          (art I g).base + BitVec.ofNat 64 (rl.offset + 4) := by
        exact hj.symm.trans hpcv
      exact (BitVec.add_right_inj _).mp h1
    have hoff' := congrArg BitVec.toNat hoff
    simp only [BitVec.toNat_ofNat] at hoff'
    have hk1 := lineOffset_succ _ k' _ hy
    have hk2 := lineOffset_succ _ (k' + 1) _ hy1
    simp only [Line.size] at hk1 hk2
    have hsum := layout_sum hFg.layout
    have hle := lineOffset_le_size (art I g).fa.lines.toList (j + 1)
    rcases Nat.lt_trichotomy (j + 1) (k' + 1) with hlt' | heq' | hgt'
    · have hmono := lineOffset_mono (art I g).fa.lines.toList (show j + 1 ≤ k' by omega)
      rw [Nat.mod_eq_of_lt (by omega : rl.offset + 4 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)] at hoff'
      omega
    · obtain rfl : j = k' := by omega
      rw [hpf _ t' hy] at hyf
      cases hyf
    · have hmono := lineOffset_mono (art I g).fa.lines.toList (show k' + 1 + 1 ≤ j + 1 by omega)
      rw [Nat.mod_eq_of_lt (by omega : rl.offset + 4 < 2 ^ 64)] at hoff'
      by_cases hx : lineOffset (art I g).fa.lines.toList (j + 1) < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hx] at hoff'
        omega
      · have hx' : lineOffset (art I g).fa.lines.toList (j + 1) = 2 ^ 64 := by omega
        rw [hx'] at hoff'
        simp at hoff'

/-- **`RunTlsN` from the register-level per-state facts** (`RunGoodL`), for an activation whose
return address is outside its code. -/
theorem runTlsN_of_good (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) : RunTlsN I B M f c := fun M' g t hR he => by
  obtain ⟨c', hRL, -, hs⟩ := reachL_of_reachNT hI hc hF hR hf hgood
    (raNotSecond_top (hF f hf) hra) (raNotTlsSecond_top (hF f hf) (tlsClosed_art hI hf) hra)
  exact tlsCf_of_good hI hF (reachN_mem hR hf) (hgood _ _ _ _ hRL he) hs he

end Lemmas

end E2E.ExecBytes
