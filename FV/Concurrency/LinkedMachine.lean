import FV.Concurrency.ArmAllocLinked
import FV.E2E.RegLevelFrame

/-!
# The linked machine of a list of compiled functions (#473, calls)

`CallSeg.WitnessC.MC2` links two compiled functions, a caller and its callee. Here any finite
list of compiled functions is linked:

* `LFn`: a compiled function, the fields of an activation (`RL`) that do not depend on the
  activation (`vc rf af fa fb lm base X psF`);
* `Link`: named compiled functions; `Link.find`, the function of a name; `Link.enter`, the entry
  of a function (its program, the pc at its base, x30 the return address, as `enterL`);
  `Link.H`, the hooks whose `bl n` enters `n`'s code;
* `Link.act`: the activation of a function of the link (`H` the link's hooks, `gv` empty);
* **`Link.M`**: the step of the function whose program the state holds (`Link.cur`), except at
  its `ret` lines (`LFn.IsRet`), where the step also switches to the program of the function
  whose code holds the return address (`Link.progAt`);
* `Link.Ok`: names distinct, code ranges pairwise disjoint (as `Nat` intervals), every function
  laid out (`layout`, `lm`), nonempty and inside the address space; the programs are then
  pairwise distinct (`prog_ne`).

Under `Link.Ok`: `agreesAt_M` (the machine agrees with every activation's step at its lines
other than `ret`), `M_eq_step` (and at every line other than `ret`, hooked ones included),
`M_bl` (a `bl n` enters `n`'s code), `M_ret`/`M_ret_prog`/`M_ret_x30` (a `ret` returns to the
program of the function holding the return address).
-/

namespace Concurrency.LinkedMachine

open Arm Backend Backend.Proof

/-! ## Compiled functions and links -/

/-- **A compiled function** (module doc): the static fields of an activation (`RL`). -/
structure LFn where
  vc : VCode
  rf : RFunc
  af : AFunc
  fa : FnAsm
  fb : FnBin
  lm : Std.HashMap Lbl Nat
  base : BitVec 64
  X : ExtSem
  psF : Backend.PState

namespace LFn

/-- The compiled function of an activation. -/
def of (R : RL) : LFn := ⟨R.vc, R.rf, R.af, R.fa, R.fb, R.lm, R.base, R.X, R.psF⟩

/-- `a` is in the code range `[base, base + 4 * words.size)` of `F`. -/
def InRange (F : LFn) (a : BitVec 64) : Prop := (a - F.base).toNat < 4 * F.fb.words.size

instance (F : LFn) (a : BitVec 64) : Decidable (F.InRange a) := by unfold InRange; infer_instance

/-- **A state at one of `F`'s `ret` lines** (as `IsRetL`). -/
def IsRet (F : LFn) (s : ArmState) : Prop :=
  ∃ j t, F.fa.lines.toList[j]? = some (.ins .ret t) ∧
    Arm.r .PC s = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j)

/-- `F` laid out as `RL.Wf` needs (`layout`, `lm`), nonempty and inside the address space. -/
structure LaidOut (F : LFn) : Prop where
  layout : F.fa.layout = .ok F.fb
  lm : labelOffsets F.fa.lines = .ok F.lm
  pos : 0 < F.fb.words.size
  fit : F.base.toNat + 4 * F.fb.words.size ≤ 2 ^ 64

end LFn

/-- **A link** (module doc): named compiled functions. -/
structure Link where
  fns : List (String × LFn)

namespace Link

/-- The function named `n` (first match). -/
def find (L : Link) (n : String) : Option LFn := (L.fns.find? (·.1 == n)).map (·.2)

/-- **Enter `F`**: its program, x30 the return address, the pc at its base (as `enterL`). -/
def enter (F : LFn) (s : ArmState) : ArmState :=
  w .PC F.base (w (.GPR 30#5) (r .PC s + 4#64) (set_program s (F.fb.program F.base)))

/-- **The link's hooks**: `bl n` enters `n`'s code (no effect if `n` is not linked); `blr` and
the TLS sequence have no effect (as `HC`). -/
def H (L : Link) : ArmHooks :=
  ⟨fun d s => match d.bind L.find with
    | some F => enter F s
    | none => s, fun _ _ s => s⟩

/-- **The activation of `F`** in the link: `L.H` its hooks, no GOT call. -/
def act (L : Link) (F : LFn) (s0 : ArmState) (K : Nat) (G : BitVec 64 → Prop) : RL :=
  { vc := F.vc, rf := F.rf, af := F.af, fa := F.fa, fb := F.fb, lm := F.lm, base := F.base, s0,
    X := F.X, H := L.H, psF := F.psF, K, G, gv := fun _ _ => False }

/-- `F`'s step in the link. -/
noncomputable def stepF (L : Link) (F : LFn) : ArmState → ArmState := ArmStepX F.X L.H F.fa

open Classical in
/-- The function whose program `s` holds (first match). -/
noncomputable def cur (L : Link) (s : ArmState) : Option LFn :=
  (L.fns.find? fun p => decide (p.2.fb.program p.2.base = s.program)).map (·.2)

/-- The program of the function whose code range holds `a` (first match), else `P`. -/
def progAt (L : Link) (a : BitVec 64) (P : Arm.Program) : Arm.Program :=
  match L.fns.find? (fun p => decide (p.2.InRange a)) with
  | some p => p.2.fb.program p.2.base
  | none => P

open Classical in
/-- **The linked machine** (module doc). -/
noncomputable def M (L : Link) (s : ArmState) : ArmState :=
  match L.cur s with
  | some F =>
    if F.IsRet s then
      set_program (L.stepF F s) (L.progAt (r .PC (L.stepF F s)) (L.stepF F s).program)
    else L.stepF F s
  | none => s

/-- Two entries of a link: distinct names, disjoint code ranges. -/
def Sep (p q : String × LFn) : Prop :=
  p.1 ≠ q.1 ∧ (p.2.base.toNat + 4 * p.2.fb.words.size ≤ q.2.base.toNat ∨
    q.2.base.toNat + 4 * q.2.fb.words.size ≤ p.2.base.toNat)

instance (p q : String × LFn) : Decidable (Sep p q) := by unfold Sep; infer_instance

/-- **A well-formed link** (module doc). -/
structure Ok (L : Link) : Prop where
  sep : L.fns.Pairwise Sep
  laid : ∀ p ∈ L.fns, p.2.LaidOut

/-! ## API -/

section api
variable {L : Link} {F : LFn} {s0 s : ArmState} {K : Nat} {G : BitVec 64 → Prop}

@[simp] theorem act_vc : (L.act F s0 K G).vc = F.vc := rfl
@[simp] theorem act_rf : (L.act F s0 K G).rf = F.rf := rfl
@[simp] theorem act_af : (L.act F s0 K G).af = F.af := rfl
@[simp] theorem act_fa : (L.act F s0 K G).fa = F.fa := rfl
@[simp] theorem act_fb : (L.act F s0 K G).fb = F.fb := rfl
@[simp] theorem act_lm : (L.act F s0 K G).lm = F.lm := rfl
@[simp] theorem act_base : (L.act F s0 K G).base = F.base := rfl
@[simp] theorem act_s0 : (L.act F s0 K G).s0 = s0 := rfl
@[simp] theorem act_X : (L.act F s0 K G).X = F.X := rfl
@[simp] theorem act_H : (L.act F s0 K G).H = L.H := rfl
@[simp] theorem act_psF : (L.act F s0 K G).psF = F.psF := rfl
@[simp] theorem act_K : (L.act F s0 K G).K = K := rfl
@[simp] theorem act_G : (L.act F s0 K G).G = G := rfl
@[simp] theorem act_gv : (L.act F s0 K G).gv = fun _ _ => False := rfl

/-- The activation's step is `F`'s step in the link. -/
theorem act_step : (L.act F s0 K G).step = ArmStepX F.X L.H F.fa := rfl

theorem act_step_stepF : (L.act F s0 K G).step = L.stepF F := rfl

theorem of_act : LFn.of (L.act F s0 K G) = F := rfl

theorem enter_pc (F : LFn) (s : ArmState) : r .PC (enter F s) = F.base := r_of_w_same

theorem enter_x30 (F : LFn) (s : ArmState) : r (.GPR 30#5) (enter F s) = r .PC s + 4#64 := by
  unfold enter
  rw [r_of_w_different (by decide), r_of_w_same]

theorem r_enter {f : StateField} (h1 : f ≠ .PC) (h2 : f ≠ .GPR 30#5) (F : LFn) (s : ArmState) :
    r f (enter F s) = r f s := by
  unfold enter
  rw [r_of_w_different h1, r_of_w_different h2]
  cases f <;> unfold Arm.r <;> rfl

theorem enter_program (F : LFn) (s : ArmState) : (enter F s).program = F.fb.program F.base := by
  simp only [enter, w_program]; rfl

theorem enter_mem (F : LFn) (s : ArmState) : (enter F s).mem = s.mem := by
  unfold enter; rw [ArmFoot.w_mem, ArmFoot.w_mem]; rfl

theorem H_call_some {n : String} (h : L.find n = some F) (s : ArmState) :
    L.H.call (some n) s = enter F s := by
  simp only [H, Option.bind_some, h]

theorem H_call_find_none {n : String} (h : L.find n = none) (s : ArmState) :
    L.H.call (some n) s = s := by
  simp only [H, Option.bind_some, h]

theorem H_call_none (s : ArmState) : L.H.call none s = s := rfl

theorem H_tls (n : String) (rg : Reg) (s : ArmState) : L.H.tls n rg s = s := rfl

end api

/-! ## Finding in a pairwise separated list -/

theorem find?_of_pairwise {α : Type} {l : List α} {p : α → Bool} {R : α → α → Prop}
    (hl : l.Pairwise R) (hR : ∀ a b, R a b → p a = true → p b = true → False) {a : α}
    (ha : a ∈ l) (hp : p a = true) : l.find? p = some a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hl
    rw [List.find?_cons]
    cases hx : p x
    · rcases List.mem_cons.1 ha with rfl | h
      · rw [hp] at hx; cases hx
      · exact ih hl.2 h
    · rcases List.mem_cons.1 ha with rfl | h
      · rfl
      · exact (hR _ _ (hl.1 a h) hx hp).elim

theorem inRange_iff {F : LFn} (hF : F.LaidOut) (a : BitVec 64) :
    F.InRange a ↔ F.base.toNat ≤ a.toNat ∧ a.toNat < F.base.toNat + 4 * F.fb.words.size := by
  have hfit := hF.fit
  have ha := a.isLt
  have hb := F.base.isLt
  unfold LFn.InRange
  rw [BitVec.toNat_sub]
  constructor
  · intro h
    by_cases hle : F.base.toNat ≤ a.toNat
    · refine ⟨hle, ?_⟩
      rw [show 2 ^ 64 - F.base.toNat + a.toNat = (a.toNat - F.base.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rintro ⟨h1, h2⟩
    rw [show 2 ^ 64 - F.base.toNat + a.toNat = (a.toNat - F.base.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem prog_head {F : LFn} (h : 0 < F.fb.words.size) :
    ∃ (w : BitVec 32) (P : List (BitVec 64 × BitVec 32)),
      F.fb.program F.base = (F.base, w) :: P := by
  match hl : F.fb.words.toList with
  | [] =>
    have : F.fb.words.size = 0 := by simpa using congrArg List.length hl
    omega
  | w :: ws =>
    refine ⟨w, wordsAt F.base 1 ws, ?_⟩
    simp only [FnBin.program, hl, wordsAt, Nat.mul_zero, BitVec.add_zero]
    rfl

/-- **Programs of separated entries are distinct.** -/
theorem prog_ne {p q : String × LFn} (hp : p.2.LaidOut) (hq : q.2.LaidOut) (h : Sep p q) :
    p.2.fb.program p.2.base ≠ q.2.fb.program q.2.base := by
  intro he
  obtain ⟨w, P, hP⟩ := prog_head hp.pos
  obtain ⟨w', P', hP'⟩ := prog_head hq.pos
  rw [hP, hP'] at he
  have hb : p.2.base = q.2.base := (Prod.mk.inj (List.cons.inj he).1).1
  have := hp.pos
  have := hq.pos
  rcases h.2 with h | h <;> rw [hb] at h <;> omega

theorem pc_inj {F : LFn} (hF : F.LaidOut) {j j' : Nat} {x x' : Insn}
    {t t' : Option Clif.TrapCode} (hj : F.fa.lines.toList[j]? = some (.ins x t))
    (hj' : F.fa.lines.toList[j']? = some (.ins x' t'))
    (he : F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j) =
      F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j')) : j = j' := by
  have hsz : (F.fa.lines.toList.map Line.size).sum ≤ 2 ^ 64 := by
    rw [layout_sum hF.layout]; have := hF.fit; omega
  have hl1 := lineOffset_le_size F.fa.lines.toList (j + 1)
  have hl2 := lineOffset_le_size F.fa.lines.toList (j' + 1)
  have hs1 := lineOffset_succ F.fa.lines.toList j _ hj
  have hs2 := lineOffset_succ F.fa.lines.toList j' _ hj'
  simp only [Line.size] at hs1 hs2
  have he2 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at he2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he2
  exact lineOffset_inj hj hj' he2

section ok
variable {L : Link} (hL : L.Ok)
include hL

theorem find_eq {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) : L.find n = some F := by
  unfold find
  rw [find?_of_pairwise hL.sep (fun a b h ha hb => h.1 (by simp at ha hb; rw [ha, hb])) hF
    (by simp)]
  rfl

theorem cur_eq {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState}
    (hs : s.program = F.fb.program F.base) : L.cur s = some F := by
  classical
  have hl : L.fns.Pairwise fun p q => p.2.fb.program p.2.base ≠ q.2.fb.program q.2.base :=
    hL.sep.imp_of_mem fun ha hb h => prog_ne (hL.laid _ ha) (hL.laid _ hb) h
  unfold cur
  rw [find?_of_pairwise hl (fun a b h ha hb => h (by simp at ha hb; rw [ha, hb])) hF
    (by simp [hs])]
  rfl

theorem progAt_eq {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {a : BitVec 64} (ha : F.InRange a)
    (P : Arm.Program) : L.progAt a P = F.fb.program F.base := by
  have hl : L.fns.Pairwise fun p q => ¬ (p.2.InRange a ∧ q.2.InRange a) :=
    hL.sep.imp_of_mem fun hp hq h => by
      rw [inRange_iff (hL.laid _ hp), inRange_iff (hL.laid _ hq)]
      have := (hL.laid _ hp).pos
      have := (hL.laid _ hq).pos
      rcases h.2 with h | h <;> omega
  unfold progAt
  rw [find?_of_pairwise hl (fun a b h ha hb => h ⟨by simpa using ha, by simpa using hb⟩) hF
    (by simpa using ha)]

open Classical in
/-- **The machine on `F`'s program.** -/
theorem M_cur {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState}
    (hs : s.program = F.fb.program F.base) :
    L.M s = if F.IsRet s then
      set_program (L.stepF F s) (L.progAt (r .PC (L.stepF F s)) (L.stepF F s).program)
    else L.stepF F s := by
  unfold M
  rw [cur_eq hL hF hs]

/-- **At every line other than `ret`** (hooked lines included) the machine is the activation's
step. -/
theorem M_eq_step {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState}
    (hs : s.program = F.fb.program F.base) (hr : ¬ F.IsRet s) (s0 : ArmState) (K : Nat)
    (G : BitVec 64 → Prop) : L.M s = (L.act F s0 K G).step s := by
  rw [M_cur hL hF hs]; simp only [hr, ↓reduceIte]; rfl

/-- A state at an instruction line other than `ret` is at no `ret` line. -/
theorem not_isRet {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : F.fa.lines.toList[j]? = some (.ins x t))
    (hx : x ≠ .ret) (hpc : r .PC s = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j)) :
    ¬ F.IsRet s := by
  rintro ⟨j', t', hj', hpc'⟩
  obtain rfl := pc_inj (show F.LaidOut from hL.laid _ hF) hj hj' (hpc.symm.trans hpc')
  rw [hj] at hj'
  cases hj'
  exact hx rfl

/-- **The linked machine agrees with every activation of a linked function** at its lines other
than `ret` (`AgreesAt`). -/
theorem agreesAt_M {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) (s0 : ArmState) (K : Nat)
    (G : BitVec 64 → Prop) : ArmAllocThread.AgreesAt (L.act F s0 K G) L.M := by
  intro s hs hn
  obtain ⟨j, x, t, hj, hx, -, hpc⟩ := hn
  exact M_eq_step hL hF hs (not_isRet hL hF hj hx hpc) s0 K G

/-- `F`'s step at a `bl m` line is the hook's call. -/
theorem stepF_bl {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState} {j : Nat}
    {m : String} {t : Option Clif.TrapCode} (hj : F.fa.lines.toList[j]? = some (.ins (.bl m) t))
    (hs : s.program = F.fb.program F.base)
    (hpc : r .PC s = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j)) :
    L.stepF F s = L.H.call (some m) s := by
  have hl : F.LaidOut := hL.laid _ hF
  have hne : F.fb.words.toList ≠ [] := by
    intro h
    have : F.fb.words.size = 0 := by simpa using congrArg List.length h
    have := hl.pos
    omega
  have hb : progBase s = F.base := progBase_eq (by rw [hs]; rfl) hne
  have hsum := layout_sum hl.layout
  have hfit := hl.fit
  have hins : insnAt F.fa (progBase s) (r .PC s) = some (.bl m) := by
    rw [hb, hpc]; exact insnAt_line (by omega) hj
  show ArmStepX F.X L.H F.fa s = _
  unfold ArmStepX
  simp only [hins]

/-- **A `bl m` of a linked function enters `m`'s code.** -/
theorem M_bl {n : String} {F F' : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState} {j : Nat}
    {m : String} {t : Option Clif.TrapCode} (hj : F.fa.lines.toList[j]? = some (.ins (.bl m) t))
    (hs : s.program = F.fb.program F.base)
    (hpc : r .PC s = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j))
    (hm : L.find m = some F') : L.M s = enter F' s := by
  rw [M_cur hL hF hs]
  simp only [not_isRet hL hF hj (by simp) hpc, ↓reduceIte]
  rw [stepF_bl hL hF hj hs hpc, H_call_some hm]

/-- **At a `ret` line** the machine is the step, the program the one of the function whose code
holds the new pc. -/
theorem M_ret {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState}
    (hs : s.program = F.fb.program F.base) (hr : F.IsRet s) :
    L.M s = set_program (L.stepF F s) (L.progAt (r .PC (L.stepF F s)) (L.stepF F s).program) := by
  rw [M_cur hL hF hs]; simp only [hr, ↓reduceIte]

/-- **A `ret` into the code of `F''`** switches to `F''`'s program. -/
theorem M_ret_prog {n n'' : String} {F F'' : LFn} (hF : (n, F) ∈ L.fns) (hF'' : (n'', F'') ∈ L.fns)
    {s : ArmState} (hs : s.program = F.fb.program F.base) (hr : F.IsRet s)
    (ha : F''.InRange (r .PC (L.stepF F s))) : (L.M s).program = F''.fb.program F''.base := by
  rw [M_ret hL hF hs hr, progAt_eq hL hF'' ha]; rfl

/-- `F`'s step at a `ret` line (without an error) jumps to x30. -/
theorem stepF_ret {n : String} {F : LFn} (hF : (n, F) ∈ L.fns) {s : ArmState}
    (hs : s.program = F.fb.program F.base) (hr : F.IsRet s) (herr : r .ERR s = .None) :
    L.stepF F s = w .PC (E2E.xreg 30 s) s := by
  obtain ⟨j, t, hj, hpc⟩ := hr
  have hl : F.LaidOut := hL.laid _ hF
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := F.X) (H := L.H) hl.layout hl.lm
    (by have := hl.fit; omega) hj rfl hs hpc herr
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset F.fa.lines.toList j, (F.lm[·]?)⟩ s
  rw [ha] at ha'
  cases ha'
  exact hstep.trans he'

/-- **The return** (module doc): at a `ret` line of `F` without an error, with the return address
x30 in the code of `F''`, the machine jumps to x30 on `F''`'s program. -/
theorem M_ret_x30 {n n'' : String} {F F'' : LFn} (hF : (n, F) ∈ L.fns) (hF'' : (n'', F'') ∈ L.fns)
    {s : ArmState} (hs : s.program = F.fb.program F.base) (hr : F.IsRet s)
    (herr : r .ERR s = .None) (ha : F''.InRange (E2E.xreg 30 s)) :
    L.M s = set_program (w .PC (E2E.xreg 30 s) s) (F''.fb.program F''.base) := by
  have hst := stepF_ret hL hF hs hr herr
  have hpc : r .PC (L.stepF F s) = E2E.xreg 30 s := by rw [hst, r_of_w_same]
  rw [M_ret hL hF hs hr, hpc, progAt_eq hL hF'' ha, hst]

end ok

end Link

end Concurrency.LinkedMachine
