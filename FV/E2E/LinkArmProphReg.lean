import FV.E2E.LinkArmProphThm

/-!
# The register prophecy (SEM1 step 2n, `docs/plans/uninit.md` §5.7)

`worldP` overlays the callee region of the VCode world with the prophecy `P n` (the actual
machine bytes at the activation's `n`-th call). The actual machine's masked registers (x0–x28
but x18, x30, the SIMD file) at that call are unrelated to the world's (`StRel.world` is
`SameWorld`), and callee-saved registers flow into the callee region (§5.7), so the canonical
callee state takes them from the actual call state too:

* `MaskedReg f`: `Masked f` but the pc; `maskedRegs` lists them (`mem_maskedRegs`);
* `regOverlay S w`: `w` with `S`'s masked registers (`r_regOverlay_in`/`_out`,
  `mem_regOverlay`, `program_regOverlay`, `regOverlay_self`, `sameWorld_regOverlay`);
* `prophStOf`: the state at call number `n` of a run (`prophStOf_call`; its memory is
  `prophOf`'s, `prophOf_eq_mem`);
* `worldPR`, `canonPR`, `progXPR`, `XPR`, `XPRI`: `worldP` overlaid with the register prophecy
  `R n`, and `canon`/`progX`/`X` of it (`progXPR_eq`); with the world's own masked registers they
  are the `P` versions (`worldPR_self`, `progXPR_self`, `XPR_call_self`); `worldPR` is the same
  world as `worldP` (`sameWorld_worldPR`).
-/

namespace E2E

open Backend Backend.Proof

/-! ## Overlaying the masked registers -/

/-- The masked registers but the pc: what a call state's register prophecy carries. -/
def MaskedReg (f : Arm.StateField) : Prop := Masked f ∧ f ≠ .PC

/-- The masked registers but the pc, as a list. -/
def maskedRegs : List Arm.StateField :=
  ((List.range 32).filter fun k => decide ((k < 29 ∧ k ≠ 18) ∨ k = 30)).map
      (fun k => .GPR (BitVec.ofNat 5 k)) ++
    (List.range 32).map fun k => .SFP (BitVec.ofNat 5 k)

theorem mem_maskedRegs (f : Arm.StateField) : f ∈ maskedRegs ↔ MaskedReg f := by
  cases f with
  | GPR i =>
    have key : ∀ j : Fin 32, (Arm.StateField.GPR (BitVec.ofFin j) ∈ maskedRegs ↔
        MaskedReg (.GPR (BitVec.ofFin j))) := by
      simp only [MaskedReg, Masked]; decide
    exact key i.toFin
  | SFP i =>
    have key : ∀ j : Fin 32, (Arm.StateField.SFP (BitVec.ofFin j) ∈ maskedRegs ↔
        MaskedReg (.SFP (BitVec.ofFin j))) := by
      simp only [MaskedReg, Masked]; decide
    exact key i.toFin
  | PC => simp only [MaskedReg, Masked]; decide
  | FLAG fl => simp only [MaskedReg, Masked]; cases fl <;> decide
  | ERR => simp only [MaskedReg, Masked]; decide
  | TPIDR => simp only [MaskedReg, Masked]; decide

/-- Copy the fields `l` of `S` into `w`. -/
def copyFields (S : Arm.ArmState) (l : List Arm.StateField) (w : Arm.ArmState) : Arm.ArmState :=
  l.foldl (fun s f => Arm.w f (Arm.r f S) s) w

theorem copyFields_r (S : Arm.ArmState) :
    ∀ (l : List Arm.StateField) (w : Arm.ArmState) (f : Arm.StateField),
      Arm.r f (copyFields S l w) = if f ∈ l then Arm.r f S else Arm.r f w
  | [], w, f => by simp [copyFields]
  | g :: l, w, f => by
    have ih := copyFields_r S l (Arm.w g (Arm.r g S) w) f
    simp only [copyFields, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hf : f ∈ l
    · simp [hf]
    · by_cases hfg : f = g
      · subst hfg; simp [hf, Arm.r_of_w_same]
      · simp [hf, hfg, Arm.r_of_w_different hfg]

theorem copyFields_mem (S : Arm.ArmState) :
    ∀ (l : List Arm.StateField) (w : Arm.ArmState), (copyFields S l w).mem = w.mem
  | [], _ => rfl
  | g :: l, w => by
    simp only [copyFields, List.foldl_cons]
    exact (copyFields_mem S l _).trans (Arm.mem_w_of_mem_eq rfl _ _)

theorem copyFields_program (S : Arm.ArmState) :
    ∀ (l : List Arm.StateField) (w : Arm.ArmState), (copyFields S l w).program = w.program
  | [], _ => rfl
  | g :: l, w => by
    simp only [copyFields, List.foldl_cons]
    exact (copyFields_program S l _).trans Arm.w_program

/-- **`w` with the masked registers (but the pc) of `S`.** -/
def regOverlay (S w : Arm.ArmState) : Arm.ArmState := copyFields S maskedRegs w

theorem r_regOverlay (S w : Arm.ArmState) (f : Arm.StateField) :
    Arm.r f (regOverlay S w) = if f ∈ maskedRegs then Arm.r f S else Arm.r f w :=
  copyFields_r S _ w f

theorem r_regOverlay_in {S w : Arm.ArmState} {f : Arm.StateField} (h : MaskedReg f) :
    Arm.r f (regOverlay S w) = Arm.r f S := by
  simp only [r_regOverlay, (mem_maskedRegs f).2 h, ↓reduceIte]

theorem r_regOverlay_out {S w : Arm.ArmState} {f : Arm.StateField} (h : ¬ MaskedReg f) :
    Arm.r f (regOverlay S w) = Arm.r f w := by
  have h' : f ∉ maskedRegs := fun h' => h ((mem_maskedRegs f).1 h')
  simp only [r_regOverlay, h', ↓reduceIte]

@[simp] theorem mem_regOverlay (S w : Arm.ArmState) : (regOverlay S w).mem = w.mem :=
  copyFields_mem S _ w

@[simp] theorem program_regOverlay (S w : Arm.ArmState) :
    (regOverlay S w).program = w.program :=
  copyFields_program S _ w

/-- **With `w`'s own masked registers the overlay is `w`.** -/
theorem regOverlay_self {S w : Arm.ArmState} (h : ∀ f, MaskedReg f → Arm.r f S = Arm.r f w) :
    regOverlay S w = w := by
  refine state_eq_of (fun f => ?_) (program_regOverlay S w) (fun a => by rw [mem_regOverlay])
  by_cases hf : MaskedReg f
  · rw [r_regOverlay_in hf]; exact h f hf
  · exact r_regOverlay_out hf

/-- **The overlay is the same world** (only masked registers change), for every frame `F`. -/
theorem sameWorld_regOverlay (F : BitVec 64 → Prop) (S w : Arm.ArmState) :
    SameWorld F w (regOverlay S w) :=
  ⟨fun f hf => (r_regOverlay_out fun h => hf h.1).symm, fun a _ => by rw [mem_regOverlay],
    (program_regOverlay S w).symm⟩

/-! ## The state at a run's call -/

open Classical in
/-- **The state prophecy of a run**: the state at call number `n` (its memory is `prophOf`'s,
its masked registers the register prophecy). -/
noncomputable def prophStOf (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) (n : Nat) : Arm.ArmState :=
  if h : ∃ i, CallPc fa base (Arm.r .PC (runX Mm i s)) ∧ callsBefore Mm fa base s i = n then
    runX Mm (Classical.choose h) s
  else s

theorem prophStOf_call {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {i : Nat} (hc : CallPc fa base (Arm.r .PC (runX Mm i s))) :
    prophStOf Mm fa base s (callsBefore Mm fa base s i) = runX Mm i s := by
  have h : ∃ j, CallPc fa base (Arm.r .PC (runX Mm j s)) ∧
      callsBefore Mm fa base s j = callsBefore Mm fa base s i := ⟨i, hc, rfl⟩
  rw [prophStOf, dite_eq_left h]
  obtain ⟨hj, he⟩ := Classical.choose_spec h
  have : Classical.choose h = i := by
    rcases Nat.lt_trichotomy (Classical.choose h) i with hlt | heq | hgt
    · exact absurd he (Nat.ne_of_lt (callsBefore_lt hj hlt))
    · exact heq
    · exact absurd he (Nat.ne_of_gt (callsBefore_lt hc hgt))
  rw [this]

/-- At a call of the run, `prophOf` is the memory of `prophStOf`. -/
theorem prophOf_eq_mem {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {i : Nat} (hc : CallPc fa base (Arm.r .PC (runX Mm i s))) :
    prophOf Mm fa base s (callsBefore Mm fa base s i) =
      (prophStOf Mm fa base s (callsBefore Mm fa base s i)).mem := by
  rw [prophOf_call hc, prophStOf_call hc]

/-- **The register prophecy holds at the run's call states**: call number `n` from the body
(`sp = c`) has the masked registers of `R n`. -/
def ProphRegOk (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (R : Nat → Arm.ArmState) : Prop :=
  ∀ i, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ f, MaskedReg f → Arm.r f (runX Mm i s) = Arm.r f (R (callsBefore Mm fa base s i))

/-- **Every run has a register prophecy**: its call states. -/
theorem prophRegOk_prophStOf (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) : ProphRegOk c Mm fa base s (prophStOf Mm fa base s) :=
  fun _ hc _ _ _ => by rw [prophStOf_call hc]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-! ## The canonical call with both prophecies -/

/-- **The world of call number `n`**: `worldP` (the prophecy bytes `Pn` in the callee region)
with the masked registers of the register prophecy `Sn`. -/
noncomputable def worldPR (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState) (w : Arm.ArmState) : Arm.ArmState :=
  regOverlay Sn (L.worldP κ M g Pn w)

/-- `canon` from `worldPR`. -/
noncomputable def canonPR (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (uses : List CV) (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState) (w : Arm.ArmState) :
    Arm.ArmState :=
  L.canon g uses (L.worldPR κ M g Pn Sn w)

open Classical in
/-- **A call of the function `g` of `P` with the prophecies `Pn`, `Sn`**: `progX` of
`worldPR`. -/
noncomputable def progXPR (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState)
    (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  L.progX κ M F g uses (L.worldPR κ M g Pn Sn w)

open Classical in
/-- **The external semantics of call number `n`** with the byte prophecies `P` and the register
prophecies `R`: as `XP`, a call of a function of `P` being `progXPR` with `P n`, `R n`. -/
noncomputable def XPR (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    ExtSem where
  call d uses w := match d with
    | some m => (match L.P.func? m with
      | some h => L.progXPR κ M F h uses (P n) (R n) w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXPR κ M F h args (P n) (R n) w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- **The calls of an activation with both prophecies**: call number `n` is `XPR … n`. -/
noncomputable def XPRI (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) :
    ExtSemI where
  call n := (L.XPR κ M g F P R n).call
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

theorem XPRI_at (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    (L.XPRI κ M g F P R).at n = L.XPR κ M g F P R n := rfl

/-- `progXPR` is `progX` of `worldPR`, and `progXP` of the register overlay. -/
theorem progXPR_eq (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV)
    (Pn : BitVec 64 → BitVec 8) (Sn w : Arm.ArmState) (M : Nat) :
    L.progXPR κ M F g uses Pn Sn w = L.progX κ M F g uses (L.worldPR κ M g Pn Sn w) := rfl

theorem XPR_prog {M : Nat} {g : Clif.Function} {m : String} {h : Clif.Function}
    (hpf : L.P.func? m = some h) (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) (uses : List CV) (w : Arm.ArmState) :
    (L.XPR κ M g F P R n).call (some m) uses w = L.progXPR κ M F h uses (P n) (R n) w := by
  simp [XPR, hpf]

/-- `worldPR`'s memory and program are `worldP`'s; its registers `Sn`'s masked ones and `w`'s
others. -/
theorem mem_worldPR {M : Nat} (g : Clif.Function) (Pn : BitVec 64 → BitVec 8) (Sn w : Arm.ArmState) :
    (L.worldPR κ M g Pn Sn w).mem = (L.worldP κ M g Pn w).mem :=
  mem_regOverlay _ _

theorem program_worldPR {M : Nat} (g : Clif.Function) (Pn : BitVec 64 → BitVec 8)
    (Sn w : Arm.ArmState) : (L.worldPR κ M g Pn Sn w).program = w.program := by
  rw [worldPR, program_regOverlay]; rfl

theorem r_worldPR_in {M : Nat} (g : Clif.Function) (Pn : BitVec 64 → BitVec 8)
    {Sn : Arm.ArmState} (w : Arm.ArmState) {f : Arm.StateField} (hf : MaskedReg f) :
    Arm.r f (L.worldPR κ M g Pn Sn w) = Arm.r f Sn :=
  r_regOverlay_in hf

theorem r_worldPR_out {M : Nat} (g : Clif.Function) (Pn : BitVec 64 → BitVec 8)
    (Sn w : Arm.ArmState) {f : Arm.StateField} (hf : ¬ MaskedReg f) :
    Arm.r f (L.worldPR κ M g Pn Sn w) = Arm.r f w := by
  rw [worldPR, r_regOverlay_out hf, worldP, r_overlay]

/-- **`worldPR` is the same world as `worldP`.** -/
theorem sameWorld_worldPR {M : Nat} (F : BitVec 64 → Prop) (g : Clif.Function)
    (Pn : BitVec 64 → BitVec 8) (Sn w : Arm.ArmState) :
    SameWorld F (L.worldP κ M g Pn w) (L.worldPR κ M g Pn Sn w) :=
  sameWorld_regOverlay F Sn _

/-! ## The world's own masked registers: the byte-prophecy contract -/

theorem worldPR_self {M : Nat} {g : Clif.Function} {Pn : BitVec 64 → BitVec 8}
    {Sn w : Arm.ArmState} (h : ∀ f, MaskedReg f → Arm.r f Sn = Arm.r f w) :
    L.worldPR κ M g Pn Sn w = L.worldP κ M g Pn w :=
  regOverlay_self fun f hf => by rw [h f hf, worldP, r_overlay]

/-- **With the world's own masked registers, `progXPR` is `progXP`.** -/
theorem progXPR_self {M : Nat} (F : BitVec 64 → Prop) {g : Clif.Function} (uses : List CV)
    {Pn : BitVec 64 → BitVec 8} {Sn w : Arm.ArmState}
    (h : ∀ f, MaskedReg f → Arm.r f Sn = Arm.r f w) :
    L.progXPR κ M F g uses Pn Sn w = L.progXP κ M F g uses Pn w := by
  rw [progXPR_eq, progXP_eq, L.worldPR_self h]

/-- **Call number `n` of `XPR` is `XP`'s from a world holding the masked registers of `R n`.** -/
theorem XPR_call_self {M : Nat} (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) (d : Option String)
    (uses : List CV) {w : Arm.ArmState} (h : ∀ f, MaskedReg f → Arm.r f (R n) = Arm.r f w) :
    (L.XPR κ M g F P R n).call d uses w = (L.XP κ M g F P n).call d uses w := by
  have hp : ∀ h' args, L.progXPR κ M F h' args (P n) (R n) w = L.progXP κ M F h' args (P n) w :=
    fun _ args => L.progXPR_self F args h
  cases d with
  | some m => simp only [XPR, XP, hp]; cases L.P.func? m <;> rfl
  | none =>
    cases uses with
    | nil => rfl
    | cons u args => simp only [XPR, XP, hp]; cases symCallee L.Xb L.P (lo64 u) <;> rfl

end LinkSys

end E2E
