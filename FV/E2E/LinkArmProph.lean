import FV.E2E.LinkArm
import FV.Backend.Proof.StaleRegion

/-!
# The prophecy-indexed call contract (SEM1 step 2, `docs/plans/uninit.md` §5.4)

`LinkSys.canon` runs a program callee from the caller's VCode world `w`, whose bytes in the
callee's stack region (below `sp`, inside the caller's `F`) are not the actual machine's. Here
the callee runs from `w` with that region overwritten (`Backend.Proof.overlay`) by a prophecy
`Pn`, the actual machine bytes there at the call; `XP … P n` is the external semantics of call
number `n`, with the prophecy `P n` (`XPI`'s `.at n`, `FV/E2E/LinkArmProphThm.lean`).

* `calleeRgn κ M g w`: the callee's stack region `StackBelow (frameDrop + κ (M - 1) g) (spv w)`
  (`Cond` places it inside `F` and outside the code image);
* `worldP`, `canonP`, `CondP`, `progXP`, `XP`: `w` overlaid, and `canon`/`Cond`/`progX`/`X` of it
  (`progXP_eq`: `progXP` is `progX` of the overlaid world);
* (a) today's contract is the special case of the world's own bytes: `worldP_self`,
  `canonP_self`, `progXP_self`, `XP_call_self`;
* (b) the canonical run reads the region only through the prophecy, and the prophecy only on the
  region: `worldP_congr`, `canonP_congr`, `condP_congr`, `progXP_congr`;
* (c) region facts: `Cond` depends on the world's registers and its memory outside `F` only
  (`cond_congr`), so `CondP ↔ Cond` (`condP_iff_cond`); with the region outside the code image
  the canonical state is `canon`'s overlaid (`canonP_eq_overlay`), the same world modulo `F`
  (`sameWorld_canonP`), with
  the prophecy inside the region and `canon`'s bytes outside (`mem_canonP_in`, `mem_canonP_out`),
  `canon`'s registers and program (`r_canonP`, `program_canonP`).
-/

namespace E2E

open Backend Backend.Proof

/-! ## State helpers -/

/-- Two states with the same registers, program and memory are equal. -/
theorem state_eq_of {s t : Arm.ArmState} (hr : ∀ f, Arm.r f s = Arm.r f t)
    (hp : s.program = t.program) (hm : ∀ a, s.mem a = t.mem a) : s = t :=
  Arm.state_eq_iff_components_eq.2 ⟨hr, hp, fun n a => read_mem_bytes_congr n a fun _ _ => hm _⟩

theorem r_w_congr {s t : Arm.ArmState} (h : ∀ f, Arm.r f s = Arm.r f t) (g : Arm.StateField)
    (v : Arm.state_value g) (f : Arm.StateField) : Arm.r f (Arm.w g v s) = Arm.r f (Arm.w g v t) := by
  by_cases hfg : f = g
  · subst hfg; rw [Arm.r_of_w_same, Arm.r_of_w_same]
  · rw [Arm.r_of_w_different hfg, Arm.r_of_w_different hfg]; exact h f

theorem r_setReg_congr {s t : Arm.ArmState} (h : ∀ f, Arm.r f s = Arm.r f t) (r : Reg) (v : CV)
    (f : Arm.StateField) : Arm.r f (setReg s r v) = Arm.r f (setReg t r v) := by
  cases r <;> simp only [setReg] <;> first | exact r_w_congr h _ _ f | exact h f

theorem placeArgs_r_congr : ∀ (rs : List Reg) (us : List CV) {s t : Arm.ArmState},
    (∀ f, Arm.r f s = Arm.r f t) → ∀ f, Arm.r f (placeArgs rs us s) = Arm.r f (placeArgs rs us t)
  | [], _, _, _, h, f => h f
  | _ :: _, [], s, t, h, f => by rw [placeArgs_nil_right, placeArgs_nil_right]; exact h f
  | r :: rs, u :: us, _, _, h, f => by
    rw [placeArgs_cons, placeArgs_cons]
    exact placeArgs_r_congr rs us (r_setReg_congr h r u) f

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-! ## The prophecy-indexed canonical call -/

/-- **The stack region of a call of `g` at depth `M` from the world `w`**: its frame and its
callees' budget below `sp` (inside `F`, outside the code image when `Cond` holds). -/
def calleeRgn (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (w : Arm.ArmState) :
    BitVec 64 → Prop :=
  StackBelow (frameDrop (L.A g).af + κ (M - 1) g) (spv w)

/-- The world `w` with the prophecy `Pn` in the stack region of a call of `g`. -/
noncomputable def worldP (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (Pn : BitVec 64 → BitVec 8) (w : Arm.ArmState) : Arm.ArmState :=
  overlay (L.calleeRgn κ M g w) Pn w

/-- **The canonical state of a call with the prophecy `Pn`**: `canon` from `w` whose callee stack
region holds `Pn`. -/
noncomputable def canonP (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (uses : List CV) (Pn : BitVec 64 → BitVec 8) (w : Arm.ArmState) : Arm.ArmState :=
  L.canon g uses (L.worldP κ M g Pn w)

/-- `Cond` of the world with the prophecy (equivalent to `Cond` of `w`, `condP_iff_cond`). -/
def CondP (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (Pn : BitVec 64 → BitVec 8) (w : Arm.ArmState) : Prop :=
  L.Cond κ M F g uses (L.worldP κ M g Pn w)

open Classical in
/-- **A call of the function `g` of `P` with the prophecy `Pn`**: the results and world of the
linked machine's call of `g` from `canonP`, when `CondP` holds and that call returned. -/
noncomputable def progXP (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8) (w : Arm.ArmState) :
    Option (List CV × Arm.ArmState) :=
  if L.CondP κ M F g uses Pn w ∧ Arm.r .ERR (L.pcall M g (L.canonP κ M g uses Pn w)) = .None then
    some ((List.range g.sig.returns.length).map fun j =>
        regVal (L.pcall M g (L.canonP κ M g uses Pn w)) (.x j),
      L.pcall M g (L.canonP κ M g uses Pn w))
  else none

open Classical in
/-- **The external semantics of call number `n` of an activation of `g` at depth `M`** with the
prophecies `P`: as `X`, a call of a function of `P` being `progXP` with the prophecy `P n`. -/
noncomputable def XP (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (n : Nat) : ExtSem where
  call d uses w := match d with
    | some m => (match L.P.func? m with
      | some h => L.progXP κ M F h uses (P n) w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXP κ M F h args (P n) w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- `progXP` is `progX` of the world with the prophecy. -/
theorem progXP_eq (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV)
    (Pn : BitVec 64 → BitVec 8) (w : Arm.ArmState) (M : Nat) :
    L.progXP κ M F g uses Pn w = L.progX κ M F g uses (L.worldP κ M g Pn w) := rfl

theorem XP_prog {M : Nat} {g : Clif.Function} {m : String} {h : Clif.Function}
    (hpf : L.P.func? m = some h) (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (n : Nat)
    (uses : List CV) (w : Arm.ArmState) :
    (L.XP κ M g F P n).call (some m) uses w = L.progXP κ M F h uses (P n) w := by
  simp [XP, hpf]

/-! ## (a) The world's own bytes: today's contract -/

theorem worldP_self {M : Nat} {g : Clif.Function} {Pn : BitVec 64 → BitVec 8} {w : Arm.ArmState}
    (h : ∀ a, L.calleeRgn κ M g w a → w.mem a = Pn a) : L.worldP κ M g Pn w = w :=
  overlay_eq_self h

/-- **With the world's own bytes as the prophecy, `canonP` is `canon`.** -/
theorem canonP_self {M : Nat} {g : Clif.Function} (uses : List CV) {Pn : BitVec 64 → BitVec 8}
    {w : Arm.ArmState} (h : ∀ a, L.calleeRgn κ M g w a → w.mem a = Pn a) :
    L.canonP κ M g uses Pn w = L.canon g uses w := by
  rw [canonP, L.worldP_self h]

/-- **With the world's own bytes as the prophecy, `progXP` is `progX`.** -/
theorem progXP_self {M : Nat} (F : BitVec 64 → Prop) {g : Clif.Function} (uses : List CV)
    {Pn : BitVec 64 → BitVec 8} {w : Arm.ArmState}
    (h : ∀ a, L.calleeRgn κ M g w a → w.mem a = Pn a) :
    L.progXP κ M F g uses Pn w = L.progX κ M F g uses w := by
  rw [progXP_eq, L.worldP_self h]

/-- **Call number `n` of `XP` is `X`'s call from a world holding the prophecy `P n` below its
`sp`** (every callee's stack region lies there). -/
theorem XP_call_self {M : Nat} (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (n : Nat) (d : Option String) (uses : List CV)
    {w : Arm.ArmState} (h : ∀ a, a.toNat < (spv w).toNat → w.mem a = P n a) :
    (L.XP κ M g F P n).call d uses w = (L.X κ M g F).call d uses w := by
  have hp : ∀ h args, L.progXP κ M F h args (P n) w = L.progX κ M F h args w :=
    fun _ args => L.progXP_self F args fun a ha => h a ha.1
  cases d with
  | some m => simp only [XP, X, hp]; cases L.P.func? m <;> rfl
  | none =>
    cases uses with
    | nil => rfl
    | cons u args => simp only [XP, X, hp]; cases symCallee L.Xb L.P (lo64 u) <;> rfl

/-- `XP` has `X`'s symbols, thread pointer and TLS flags. -/
theorem XP_sym_tp_tls {M : Nat} (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (n : Nat) :
    (L.XP κ M g F P n).sym = (L.X κ M g F).sym ∧ (L.XP κ M g F P n).tp = (L.X κ M g F).tp ∧
      (L.XP κ M g F P n).tlsFlags = (L.X κ M g F).tlsFlags :=
  ⟨rfl, rfl, rfl⟩

/-! ## (b) The prophecy and the world -/

/-- **`worldP` reads the world's region only through the prophecy, and the prophecy only on the
region.** -/
theorem worldP_congr {M : Nat} {g : Clif.Function} {Pn Pn' : BitVec 64 → BitVec 8}
    {w w' : Arm.ArmState} (hr : ∀ f, Arm.r f w = Arm.r f w') (hp : w.program = w'.program)
    (hm : ∀ a, ¬ L.calleeRgn κ M g w a → w.mem a = w'.mem a)
    (hP : ∀ a, L.calleeRgn κ M g w a → Pn a = Pn' a) :
    L.worldP κ M g Pn w = L.worldP κ M g Pn' w' := by
  have hrg : L.calleeRgn κ M g w' = L.calleeRgn κ M g w := by
    simp only [calleeRgn, spv, hr]
  refine state_eq_of (fun f => ?_) hp (fun a => ?_)
  · simp only [worldP, r_overlay]; exact hr f
  · simp only [worldP]
    rw [hrg]
    by_cases ha : L.calleeRgn κ M g w a
    · rw [mem_overlay_in ha, mem_overlay_in ha]; exact hP a ha
    · rw [mem_overlay_out ha, mem_overlay_out ha]; exact hm a ha

/-- **The canonical state with a prophecy depends on the world's registers, program and memory
outside the callee's region, and on the prophecy inside it.** -/
theorem canonP_congr {M : Nat} {g : Clif.Function} (uses : List CV)
    {Pn Pn' : BitVec 64 → BitVec 8} {w w' : Arm.ArmState} (hr : ∀ f, Arm.r f w = Arm.r f w')
    (hp : w.program = w'.program) (hm : ∀ a, ¬ L.calleeRgn κ M g w a → w.mem a = w'.mem a)
    (hP : ∀ a, L.calleeRgn κ M g w a → Pn a = Pn' a) :
    L.canonP κ M g uses Pn w = L.canonP κ M g uses Pn' w' := by
  rw [canonP, canonP, L.worldP_congr hr hp hm hP]

theorem condP_congr {M : Nat} (F : BitVec 64 → Prop) {g : Clif.Function} (uses : List CV)
    {Pn Pn' : BitVec 64 → BitVec 8} {w w' : Arm.ArmState} (hr : ∀ f, Arm.r f w = Arm.r f w')
    (hp : w.program = w'.program) (hm : ∀ a, ¬ L.calleeRgn κ M g w a → w.mem a = w'.mem a)
    (hP : ∀ a, L.calleeRgn κ M g w a → Pn a = Pn' a) :
    L.CondP κ M F g uses Pn w ↔ L.CondP κ M F g uses Pn' w' := by
  rw [CondP, CondP, L.worldP_congr hr hp hm hP]

/-- **`progXP` depends on the world's registers, program and memory outside the callee's region,
and on the prophecy inside it.** -/
theorem progXP_congr {M : Nat} (F : BitVec 64 → Prop) {g : Clif.Function} (uses : List CV)
    {Pn Pn' : BitVec 64 → BitVec 8} {w w' : Arm.ArmState} (hr : ∀ f, Arm.r f w = Arm.r f w')
    (hp : w.program = w'.program) (hm : ∀ a, ¬ L.calleeRgn κ M g w a → w.mem a = w'.mem a)
    (hP : ∀ a, L.calleeRgn κ M g w a → Pn a = Pn' a) :
    L.progXP κ M F g uses Pn w = L.progXP κ M F g uses Pn' w' := by
  rw [progXP_eq, progXP_eq, L.worldP_congr hr hp hm hP]

/-! ## (c) Region facts -/

/-- **`Cond` depends on the world's registers and its memory outside `F` only.** -/
theorem cond_congr {M : Nat} {F : BitVec 64 → Prop} {g : Clif.Function} {uses : List CV}
    {w w' : Arm.ArmState} (hr : ∀ f, Arm.r f w = Arm.r f w')
    (hm : ∀ a, ¬ F a → w.mem a = w'.mem a) :
    L.Cond κ M F g uses w ↔ L.Cond κ M F g uses w' := by
  have key : ∀ {w w' : Arm.ArmState}, (∀ f, Arm.r f w = Arm.r f w') →
      (∀ a, ¬ F a → w.mem a = w'.mem a) → L.Cond κ M F g uses w → L.Cond κ M F g uses w' := by
    intro w w' hr hm h
    have hsp : spv w = spv w' := hr _
    obtain ⟨hM, herr, hal, hroom, hdead, vals, cm, cs, rvals, cm', hmr, hargs, hsav, hpl, hinit,
      hret⟩ := h
    refine ⟨hM, by rw [← hr]; exact herr, by rw [← hsp]; exact hal, by rw [← hsp]; exact hroom,
      by rw [← hsp]; exact hdead, vals, cm, cs, rvals, cm', ⟨fun a b hv hb => ?_, hmr.valid,
      hmr.symbols⟩, ⟨hargs.1, hargs.2.1, fun off v hv => ?_⟩, fun off v hv => ?_,
      by rw [← hsp]; exact hpl, hinit, hret⟩
    · rw [← hmr.bytes a b hv hb]
      simp only [Arm.read_mem, Arm.read_store]
      exact (hm _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))).symm
    · rw [← hargs.2.2 off v hv]
      have hs : spOf w' = spv w := hsp.symm
      show (Arm.read_mem_bytes v.ty.bytes (spOf w' + BitVec.ofNat 64 off) w').setWidth v.ty.width =
        (Arm.read_mem_bytes v.ty.bytes (spOf w + BitVec.ofNat 64 off) w).setWidth v.ty.width
      rw [hs, read_mem_bytes_congr _ _ fun k hk => (hm _ (hsav off v hv k hk)).symm]
      rfl
    · rw [← hsp]; exact hsav off v hv
  exact ⟨key hr hm, key (fun f => (hr f).symm) fun a ha => (hm a ha).symm⟩

/-- **`CondP` is `Cond` of the world**: the prophecy is inside `F`. -/
theorem condP_iff_cond {M : Nat} {F : BitVec 64 → Prop} {g : Clif.Function} {uses : List CV}
    {Pn : BitVec 64 → BitVec 8} {w : Arm.ArmState} :
    L.CondP κ M F g uses Pn w ↔ L.Cond κ M F g uses w := by
  have hr : ∀ f, Arm.r f w = Arm.r f (L.worldP κ M g Pn w) := fun f => (r_overlay f w).symm
  have hrg : L.calleeRgn κ M g (L.worldP κ M g Pn w) = L.calleeRgn κ M g w := by
    simp only [calleeRgn, spv, ← hr]
  have hm : (∀ a, L.calleeRgn κ M g w a → F a) →
      ∀ a, ¬ F a → w.mem a = (L.worldP κ M g Pn w).mem a :=
    fun hR a ha => (mem_overlay_out fun h' => ha (hR a h')).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hR : ∀ a, L.calleeRgn κ M g (L.worldP κ M g Pn w) a → F a ∧ ¬ L.Img a := h.2.2.2.2.1
    rw [hrg] at hR
    exact (L.cond_congr hr (hm fun a ha => (hR a ha).1)).2 h
  · exact (L.cond_congr hr (hm fun a ha => (h.2.2.2.2.1 a ha).1)).1 h

theorem r_canonP {M : Nat} (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8)
    (w : Arm.ArmState) (f : Arm.StateField) :
    Arm.r f (L.canonP κ M g uses Pn w) = Arm.r f (L.canon g uses w) := by
  simp only [canonP, canon]
  refine r_w_congr (placeArgs_r_congr _ _ fun f => ?_) _ _ f
  rw [r_withImg, r_withImg, worldP, r_overlay]

theorem program_canonP {M : Nat} (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8)
    (w : Arm.ArmState) : (L.canonP κ M g uses Pn w).program = (L.canon g uses w).program := by
  rw [canonP, L.program_canon, L.program_canon]; rfl

theorem mem_canonP_in {M : Nat} {g : Clif.Function} (uses : List CV) {Pn : BitVec 64 → BitVec 8}
    {w : Arm.ArmState} {a : BitVec 64} (hI : ¬ L.Img a) (ha : L.calleeRgn κ M g w a) :
    (L.canonP κ M g uses Pn w).mem a = Pn a := by
  rw [canonP, L.mem_canon, mem_withImg]
  simp only [hI, ↓reduceIte, worldP]
  exact mem_overlay_in ha

theorem mem_canonP_out {M : Nat} {g : Clif.Function} (uses : List CV) {Pn : BitVec 64 → BitVec 8}
    {w : Arm.ArmState} {a : BitVec 64} (ha : ¬ L.calleeRgn κ M g w a) :
    (L.canonP κ M g uses Pn w).mem a = (L.canon g uses w).mem a := by
  rw [canonP, L.mem_canon, L.mem_canon, mem_withImg, mem_withImg, worldP, mem_overlay_out ha]

/-- **With the region outside the code image, `canonP` is `canon` overlaid by the prophecy.** -/
theorem canonP_eq_overlay {M : Nat} {g : Clif.Function} (uses : List CV)
    {Pn : BitVec 64 → BitVec 8} {w : Arm.ArmState} (hI : ∀ a, L.calleeRgn κ M g w a → ¬ L.Img a) :
    L.canonP κ M g uses Pn w = overlay (L.calleeRgn κ M g w) Pn (L.canon g uses w) := by
  refine state_eq_of (fun f => ?_) ?_ (fun a => ?_)
  · rw [r_overlay]; exact L.r_canonP g uses Pn w f
  · rw [program_overlay]; exact L.program_canonP g uses Pn w
  · by_cases ha : L.calleeRgn κ M g w a
    · rw [mem_overlay_in ha]; exact L.mem_canonP_in uses (hI a ha) ha
    · rw [mem_overlay_out ha]; exact L.mem_canonP_out uses ha

/-- **With the region inside `F` and outside the code image (as `Cond` places it), `canonP` is the
same world as `canon` modulo `F`.** -/
theorem sameWorld_canonP {M : Nat} {F : BitVec 64 → Prop} {g : Clif.Function} (uses : List CV)
    {w : Arm.ArmState} (hR : ∀ a, L.calleeRgn κ M g w a → F a ∧ ¬ L.Img a)
    (Pn : BitVec 64 → BitVec 8) :
    SameWorld F (L.canon g uses w) (L.canonP κ M g uses Pn w) := by
  rw [L.canonP_eq_overlay uses fun a ha => (hR a ha).2]
  exact sameWorld_overlay (fun a ha => (hR a ha).1) _

end LinkSys

end E2E
