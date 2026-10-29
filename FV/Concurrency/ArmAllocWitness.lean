import FV.Concurrency.ArmAllocStraight
import FV.Concurrency.ThreadLayerWitness
import FV.E2E.Binary

/-!
# Non-vacuity of layer 4b on a compiled function (T2h, #311)

A concrete activation (`RL`) of a compiled function: the VCode `vc`, its allocation `rf`,
lowered, emitted and laid out by the compiler (`lowerRFunc`, `emitFunc`, `layout`), loaded at
`0x10000` in an ABI entry state `s0` (code words in memory, `sp = 0x8000`). `R.Wf` holds, the
register-level relation `Q ∧ AInv` holds after the prologue (`Backend.Proof.q_init`), so the
premises of the layer-4b theorems are satisfiable:

* `noev_premises`: `args; rets` (`arm_alloc_refines_noev`'s scope).
-/

namespace Concurrency.ArmAllocThread.Witness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread
open E2E (spv xreg StackAvail StackRoom CodeAddr AbiCall)

theorem ok_getD {ε α : Type} [Inhabited α] {e : Except ε α} (h : e.toBool = true) :
    e = .ok (e.toOption.getD default) := by
  cases e <;> simp_all [Except.toBool, Except.toOption]

/-- A probed stack below 4 KiB gets no stack probes (#581). -/
theorem probeCount_small {total : Nat} (h : total < 4096) : probeCount total = 0 := by
  simp [probeCount, Nat.div_eq_of_lt h]

/-- A frame below 4 KiB (with its callees' 16-byte setup area) gets no stack probes, so none
below it (#581). -/
theorem probeBelow_small {af : AFunc} (h : af.frameSize + 16 < 4096) : E2E.probeBelow af = 0 := by
  have ht : probeTotal af.frameSize af.isCaller < 4096 := by unfold probeTotal; split <;> omega
  simp [E2E.probeBelow, probeCount_small ht]

/-- `StackAvail`'s probe budget for a frame below 4 KiB: any budget (#581). -/
theorem probeBelow_le_small {af : AFunc} {K : Nat} (h : af.frameSize + 16 < 4096) :
    E2E.probeBelow af ≤ K := by
  rw [probeBelow_small h]; exact Nat.zero_le _

/-- The code words of `fb` at `base`, as memory (zero elsewhere). -/
def codeMem (fb : FnBin) (base : BitVec 64) : Memory := fun a =>
  let k := (a - base).toNat
  if k < 4 * fb.words.size then (fb.words[k / 4]!).extractLsb' (8 * (k % 4)) 8 else 0

/-- The ABI entry state: `fb` loaded at `base` (program and memory), `sp = 0x8000`, return
address `0x4000`. -/
def entry (fb : FnBin) (base : BitVec 64) : ArmState :=
  setMem (codeMem fb base) (w .PC base (w (.GPR 31#5) 0x8000#64 (w (.GPR 30#5) 0x4000#64
    (set_program ArmState.default (fb.program base)))))

/-- The activation of the compiled `vc`, `rf` (no callee, no kept address, no GOT call). -/
def act (vc : VCode) (rf : RFunc) : RL :=
  let af := (lowerRFunc vc rf).toOption.getD default
  let fa := (emitFunc 0 af).toOption.getD default
  let fb := fa.layout.toOption.getD default
  { vc, rf, af, fa, fb
    lm := (labelOffsets fa.lines).toOption.getD default
    base := 0x10000#64
    s0 := entry fb 0x10000#64
    X := VCodeThread.Witness.X0
    H := ⟨fun _ s => s, fun _ _ s => s⟩
    psF := ((blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {}).toOption.map (·.2)).getD {}
    K := 0
    G := fun _ => False
    gv := fun _ _ => False }

/-- `args; rets`. -/
def vcN : VCode :=
  { name := "w", blocks := #[{ label := 0, insts := #[.args [], .rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def rfN : RFunc := { blocks := #[#[.op 0 #[], .op 1 #[]]], spillSlots := 0, saved := [] }

abbrev RN : RL := act vcN rfN

/-! ## The activation's facts -/

theorem room_of {n : Nat} (hn : n ≤ 0x1000) {a p : BitVec 64} (hp1 : 0x10000 ≤ p.toNat)
    (hp2 : p.toNat < 0x20000) (hd : (a - p).toNat < 4) :
    n ≤ (a - (0x8000#64 - BitVec.ofNat 64 n)).toNat := by
  bv_omega

theorem wordsAt_addr {base : BitVec 64} : ∀ {k : Nat} {ws : List (BitVec 32)}
    {p : BitVec 64 × BitVec 32}, List.Mem p (wordsAt base k ws) →
    ∃ j < ws.length, p.1 = base + BitVec.ofNat 64 (4 * (k + j))
  | _, [], _, h => nomatch h
  | k, w :: ws, p, h => by
    cases h with
    | head => exact ⟨0, by simp, rfl⟩
    | tail _ h =>
      obtain ⟨j, hj, he⟩ := wordsAt_addr h
      exact ⟨j + 1, by simp; omega, by rw [he]; congr 3; omega⟩

theorem entry_program (fb : FnBin) (base : BitVec 64) : (entry fb base).program = fb.program base := by
  simp [entry, setMem_program, Arm.w_program, set_program]

theorem ok_snd {ε α β : Type} {e : Except ε (α × β)} {d : β} (h : e.toBool = true) :
    ∃ x, e = .ok (x, (e.toOption.map (·.2)).getD d) := by
  cases e with
  | error _ => simp [Except.toBool] at h
  | ok r => exact ⟨r.1, by simp [Except.toOption]⟩

theorem wf_of {vc : VCode} {rf : RFunc}
    (hc : checkAlloc vc rf = .ok ())
    (ha : (lowerRFunc vc rf).toBool = true)
    (he : (emitFunc 0 (act vc rf).af).toBool = true)
    (hk : (act vc rf).fa.k = 0)
    (hl : (act vc rf).fa.layout.toBool = true)
    (hm : (labelOffsets (act vc rf).fa.lines).toBool = true)
    (hfit : 4 * (act vc rf).fb.words.size ≤ 2 ^ 64)
    (hfs : (act vc rf).af.frameSize ≤ 0x100)
    (hsz : 4 * (act vc rf).fb.words.size ≤ 0x10000)
    (hps : (blocksLinesE (act vc rf).ctx (act vc rf).af (act vc rf).af.blocks.toList {}).toBool =
      true) :
    (act vc rf).Wf where
  check := allocChecked_of_checkAlloc hc
  alloc := ok_getD ha
  emit := by rw [hk]; exact ok_getD he
  layout := ok_getD hl
  lm := ok_getD hm
  fit := hfit
  stack := by
    have hsp : spv (act vc rf).s0 = 0x8000#64 := by
      simp [spv, act, entry, ArmFoot.r_setMem, Arm.r_of_w_different, Arm.r_of_w_same]
    have hK : (act vc rf).K = 0 := rfl
    refine ⟨⟨?_, fun a ⟨p, hp, hd⟩ => ?_⟩, ?_⟩
    · rw [hsp, hK]; simp; omega
    · rw [hsp, hK]
      have hp' : List.Mem p (wordsAt 0x10000#64 0 (act vc rf).fb.words.toList) := by
        have e := entry_program (act vc rf).fb 0x10000#64
        simp only [FnBin.program] at e
        exact e ▸ hp
      obtain ⟨j, hj, he⟩ := wordsAt_addr hp'
      have hjs : j < (act vc rf).fb.words.size := by simpa using hj
      have hp1 : p.1.toNat = 0x10000 + 4 * j := by
        rw [he]; simp only [Nat.zero_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact room_of (by omega) (by omega) (by omega) hd
    · exact Nat.le_of_eq (probeBelow_small (af := (act vc rf).af) (by omega))
  psF := ok_snd hps
  prog0 := entry_program _ _
  gfree := fun _ h => h.elim


theorem spv_s0 (vc : VCode) (rf : RFunc) : spv (act vc rf).s0 = 0x8000#64 := by
  simp [spv, act, entry, ArmFoot.r_setMem, Arm.r_of_w_different, Arm.r_of_w_same]

theorem abi_of {vc : VCode} {rf : RFunc} (hsz : 4 * (act vc rf).fb.words.size ≤ 0x10000)
    (hcode : ∀ k < (act vc rf).fb.words.size,
      Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) (act vc rf).s0 =
        (act vc rf).fb.words[k]!) :
    AbiCall (act vc rf).fb (act vc rf).base 0x4000#64 (act vc rf).s0 where
  program := entry_program _ _
  code k w hk := by
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
    show Arm.read_mem_bytes 4 (0x10000#64 + _) _ = _
    rw [hcode k hlt]
    simp [getElem!_def, hlt]
  pc := by simp [act, entry, ArmFoot.r_setMem, Arm.r_of_w_same]
  err := by
    simp only [act, entry, ArmFoot.r_setMem, Arm.r_of_w_different (show StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 31#5 by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 30#5 by simp)]
    simp [set_program, ArmState.default, Arm.r, read_base_error]
  lr := by simp [xreg, act, entry, ArmFoot.r_setMem, Arm.r_of_w_different, Arm.r_of_w_same]
  spAligned := by rw [spv_s0]; decide
  fits := by show (0x10000#64 : BitVec 64).toNat + _ ≤ _; simp; omega

/-! ## Activations at another stack pointer and code address

Threads of a program run on disjoint stacks and (their frame sets include their code) disjoint
code: `actAt sp base` is `act` with `sp` at the entry, its code at `base`. -/

/-- The ABI entry state with `sp` at the entry (as `entry`). -/
def entryAt (sp : BitVec 64) (fb : FnBin) (base : BitVec 64) : ArmState :=
  setMem (codeMem fb base) (w .PC base (w (.GPR 31#5) sp (w (.GPR 30#5) 0x4000#64
    (set_program ArmState.default (fb.program base)))))

/-- The activation of the compiled `vc`, `rf` entered with `sp`, its code at `base` (as `act`). -/
def actAt (sp base : BitVec 64) (vc : VCode) (rf : RFunc) : RL :=
  { act vc rf with base := base, s0 := entryAt sp (act vc rf).fb base }

theorem entryAt_program (sp : BitVec 64) (fb : FnBin) (base : BitVec 64) :
    (entryAt sp fb base).program = fb.program base := by
  simp [entryAt, setMem, set_program, w, write_base_gpr, write_base_pc]

theorem spv_s0At (sp base : BitVec 64) (vc : VCode) (rf : RFunc) :
    spv (actAt sp base vc rf).s0 = sp := by
  simp [spv, actAt, entryAt, ArmFoot.r_setMem, Arm.r_of_w_different, Arm.r_of_w_same]

theorem room_ofAt {n : Nat} {sp base : BitVec 64} (hn : n ≤ 0x1000) (hsp : n ≤ sp.toNat)
    (hsp2 : sp.toNat ≤ 0x8000) (hb1 : 0x10000 ≤ base.toNat) (hb2 : base.toNat ≤ 0x100000)
    {a p : BitVec 64} (hp1 : base.toNat ≤ p.toNat)
    (hp2 : p.toNat < base.toNat + 0x10000) (hd : (a - p).toNat < 4) :
    n ≤ (a - (sp - BitVec.ofNat 64 n)).toNat := by
  bv_omega

theorem wf_ofAt {sp base : BitVec 64} (hsp1 : 0x1000 ≤ sp.toNat) (hsp2 : sp.toNat ≤ 0x8000)
    (hb1 : 0x10000 ≤ base.toNat) (hb2 : base.toNat ≤ 0x100000)
    {vc : VCode} {rf : RFunc} (hc : checkAlloc vc rf = .ok ())
    (ha : (lowerRFunc vc rf).toBool = true)
    (he : (emitFunc 0 (act vc rf).af).toBool = true)
    (hk : (act vc rf).fa.k = 0)
    (hl : (act vc rf).fa.layout.toBool = true)
    (hm : (labelOffsets (act vc rf).fa.lines).toBool = true)
    (hfit : 4 * (act vc rf).fb.words.size ≤ 2 ^ 64)
    (hfs : (act vc rf).af.frameSize ≤ 0x100)
    (hsz : 4 * (act vc rf).fb.words.size ≤ 0x10000)
    (hps : (blocksLinesE (act vc rf).ctx (act vc rf).af (act vc rf).af.blocks.toList {}).toBool =
      true) :
    (actAt sp base vc rf).Wf where
  check := allocChecked_of_checkAlloc hc
  alloc := ok_getD ha
  emit := by rw [show (actAt sp base vc rf).fa.k = 0 from hk]; exact ok_getD he
  layout := ok_getD hl
  lm := ok_getD hm
  fit := hfit
  stack := by
    have hsp := spv_s0At sp base vc rf
    have hK : (actAt sp base vc rf).K = 0 := rfl
    refine ⟨⟨?_, fun a ⟨p, hp, hd⟩ => ?_⟩, ?_⟩
    · rw [hsp, hK]; show (act vc rf).af.frameSize + 16 + 0 ≤ _; omega
    · rw [hsp, hK]
      have hp' : List.Mem p (wordsAt base 0 (act vc rf).fb.words.toList) := by
        have e := entryAt_program sp (act vc rf).fb base
        simp only [FnBin.program] at e
        exact e ▸ hp
      obtain ⟨j, hj, he⟩ := wordsAt_addr hp'
      have hjs : j < (act vc rf).fb.words.size := by simpa using hj
      have hp1 : p.1.toNat = base.toNat + 4 * j := by
        rw [he]; simp only [Nat.zero_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact room_ofAt (by show (act vc rf).af.frameSize + 16 + 0 ≤ _; omega)
        (by show (act vc rf).af.frameSize + 16 + 0 ≤ _; omega) hsp2 hb1 hb2 (by omega)
        (by omega) hd
    · exact Nat.le_of_eq (probeBelow_small (show (act vc rf).af.frameSize + 16 < 4096 by omega))
  psF := ok_snd hps
  prog0 := entryAt_program _ _ _
  gfree := fun _ h => h.elim

theorem abi_ofAt {sp base : BitVec 64} (hal : sp.toNat % 16 = 0) (hb2 : base.toNat ≤ 0x100000)
    {vc : VCode} {rf : RFunc}
    (hsz : 4 * (act vc rf).fb.words.size ≤ 0x10000)
    (hcode : ∀ k < (act vc rf).fb.words.size,
      Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) (actAt sp base vc rf).s0 =
        (act vc rf).fb.words[k]!) :
    AbiCall (actAt sp base vc rf).fb (actAt sp base vc rf).base 0x4000#64 (actAt sp base vc rf).s0 where
  program := entryAt_program _ _ _
  code k w hk := by
    have efb : (actAt sp base vc rf).fb = (act vc rf).fb := rfl
    rw [efb] at hk
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
    show Arm.read_mem_bytes 4 (base + _) _ = _
    rw [hcode k hlt]
    simp [getElem!_def, hlt]
  pc := by simp [actAt, entryAt, act, ArmFoot.r_setMem, Arm.r_of_w_same]
  err := by
    simp only [actAt, entryAt, ArmFoot.r_setMem,
      Arm.r_of_w_different (show StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 31#5 by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 30#5 by simp)]
    simp [set_program, ArmState.default, Arm.r, read_base_error]
  lr := by simp [xreg, actAt, entryAt, ArmFoot.r_setMem, Arm.r_of_w_different, Arm.r_of_w_same]
  spAligned := by rw [spv_s0At]; exact hal
  fits := by
    show base.toNat + 4 * (act vc rf).fb.words.size ≤ _; omega

/-- The register-level relation holds after the prologue of the activation. -/
theorem q_of {vc : VCode} {rf : RFunc} (hR : (act vc rf).Wf)
    (hsz : 4 * (act vc rf).fb.words.size ≤ 0x10000)
    (hcode : ∀ k < (act vc rf).fb.words.size,
      Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) (act vc rf).s0 =
        (act vc rf).fb.words[k]!)
    (hA : ∀ r, (act vc rf).vc.EntryArg r → r.isArgReg = true) :
    ∃ s c, Q (act vc rf) s c ∧ AInv (act vc rf) c := by
  obtain ⟨n, -, hq, hA', -⟩ := q_init hR (abi_of hsz hcode)
    ((E2E.Binary.bodyEntry_bodyOf (act vc rf).af (act vc rf).s0).w (act vc rf).F hA)
  exact ⟨_, _, hq, hA'⟩

/-! ## Layout without hashing (one label)

`labelOffsets` builds a hash map, whose hash function the kernel does not reduce. For lines with
one label, at the front, the map is `∅.insert l 0` (`labelOffsets_one`, by the hash map's
lemmas), and `layout` is `layoutAt` of that map, which the kernel evaluates when no instruction
refers to a label (the map is never queried). -/

/-- The first label of lines that start with their only label. -/
def headLabel : List Line → Lbl
  | .label l :: _ => l
  | _ => .block 0

def oneLabel : List Line → Bool
  | .label _ :: rest => rest.all (!·.isLabel)
  | _ => false

theorem go_noLabel : ∀ (ls : List Line) (off : Nat) (m : Std.HashMap Lbl Nat),
    (ls.all (!·.isLabel)) = true → labelOffsets.go ls off m = .ok m
  | [], _, _, _ => rfl
  | ln :: ls, off, m, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases ln with
    | label l => simp [Line.isLabel] at h
    | ins i t => simp only [labelOffsets.go]; exact go_noLabel ls _ m h.2
    | word a b => simp only [labelOffsets.go]; exact go_noLabel ls _ m h.2

theorem labelOffsets_one {lines : Array Line} (h : oneLabel lines.toList = true) :
    labelOffsets lines = .ok ((∅ : Std.HashMap Lbl Nat).insert (headLabel lines.toList) 0) := by
  obtain ⟨l, rest, hl, hr⟩ : ∃ l rest, lines.toList = .label l :: rest ∧
      rest.all (!·.isLabel) = true := by
    revert h
    generalize lines.toList = L
    intro h
    cases L with
    | nil => simp [oneLabel] at h
    | cons ln rest =>
      cases ln with
      | label l => exact ⟨l, rest, rfl, h⟩
      | _ => simp [oneLabel] at h
  unfold labelOffsets
  rw [hl]
  simp only [labelOffsets.go, headLabel]
  rw [show ({} : Std.HashMap Lbl Nat) = ∅ from rfl, Std.HashMap.contains_empty]
  exact go_noLabel rest 0 _ hr

/-- `FnAsm.layout` with the label map given. -/
def layoutAt (f : FnAsm) (lbls : Std.HashMap Lbl Nat) : Except String FnBin := do
  let lbl (l : Lbl) : Option Nat := lbls[l]?
  let code := codeLines f.lines.toList
  let ctx (pc : Nat) (ln : Line) (e : String) : String := match ln with
    | .ins i _ => s!"{f.name}+{pc}: `{i.asm f.k}`: {e}"
    | _ => s!"{f.name}+{pc}: {e}"
  let words ← encodeCode ctx lbl code #[]
  if 4 * words.size != f.size then throw s!"{f.name}: size {4 * words.size} ≠ {f.size}"
  let traps := codeTraps code
  if traps != f.traps then throw s!"{f.name}: trap table differs from the trap sites"
  pure { name := f.name, words, relocs := codeRelocs code, traps,
         insns := (codeInsns code).toArray }

theorem layout_eq {f : FnAsm} {M : Std.HashMap Lbl Nat} (h : labelOffsets f.lines = .ok M) :
    f.layout = layoutAt f M := by
  unfold FnAsm.layout layoutAt
  rw [h]
  rfl

/-- The laid-out code of `act vc rf`, kernel-reducible (one label). -/
def fbK (vc : VCode) (rf : RFunc) : FnBin :=
  (layoutAt (act vc rf).fa
    ((∅ : Std.HashMap Lbl Nat).insert (headLabel (act vc rf).fa.lines.toList) 0)).toOption.getD default

theorem fb_eq {vc : VCode} {rf : RFunc} (h : oneLabel (act vc rf).fa.lines.toList = true) :
    (act vc rf).fb = fbK vc rf := by
  show (act vc rf).fa.layout.toOption.getD default = _
  rw [layout_eq (labelOffsets_one h)]
  rfl

/-! ## `args; rets` -/

theorem oneN : oneLabel RN.fa.lines.toList = true := by decide +kernel

theorem wfN : RN.Wf := by
  have hfb := fb_eq oneN
  refine wf_of (VCodeThread.Witness.ok_of_isOkB () (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ (by decide +kernel) ?_ (by decide +kernel)
  · rw [layout_eq (labelOffsets_one oneN)]; decide +kernel
  · rw [labelOffsets_one oneN]; rfl
  · rw [hfb]; decide +kernel
  · rw [hfb]; decide +kernel

theorem qN : ∃ s c, Q RN s c ∧ AInv RN c := by
  have hfb := fb_eq oneN
  refine q_of wfN (by rw [hfb]; decide +kernel) ?_ fun r ⟨vb, ds, h1, h2, v, hv⟩ => ?_
  · have hs0 : RN.s0 = entry (fbK vcN rfN) 0x10000#64 := by
      show entry RN.fb _ = _; rw [hfb]
    rw [hs0, hfb]
    decide +kernel
  · simp only [RN, act, vcN] at h1
    cases h1
    simp at h2
    subst h2
    simp at hv

theorem scopeN : NoEvScope RN := by
  intro b vb k i hb hi
  rcases b with _ | b
  · simp only [RN, act, vcN] at hb
    cases hb
    rcases k with _ | _ | k
    · simp at hi; subst hi; exact .inr (.inl ⟨_, rfl⟩)
    · simp at hi; subst hi; exact .inr (.inr (.inl ⟨_, rfl⟩))
    · simp at hi
  · simp [RN, act, vcN] at hb

theorem noMovesN : NoMoves RN := by
  intro b items hb src dst hm
  rcases b with _ | b
  · simp only [RN, act, rfN] at hb
    cases hb
    simp at hm
  · simp [RN, act, rfN] at hb

/-- **Non-vacuity of `arm_alloc_refines_noev`**: the compiled `args; rets` (`RN`) satisfies its
premises: `R.Wf`, the scope, no moves, and a state related by `Q ∧ AInv` (after the prologue);
the theorem then applies to every precise Arm run from that state. -/
theorem noev_premises : RN.Wf ∧ NoEvScope RN ∧ NoMoves RN ∧ ∃ s c, Q RN s c ∧ AInv RN c ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RN.step (fun _ _ => True) (s, mon) ls t' →
      ∃ n trS cE ψ, n ≤ ls.length ∧ AllocThread.MTRun RN.vc RN.rf RN.sem ckeep (cEvs RN.F RN.ctx) c trS cE ∧
        ThreadRefine.Refines (· = ·) (PrivA RN) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done RN cE) := by
  obtain ⟨s, c, hq, hA⟩ := qN
  exact ⟨wfN, scopeN, noMovesN, s, c, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_noev wfN scopeN noMovesN hq hA hr⟩

end Concurrency.ArmAllocThread.Witness
