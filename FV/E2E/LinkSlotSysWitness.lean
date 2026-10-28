import FV.E2E.LinkPlaceBLeave
import FV.E2E.LinkCheck
import FV.E2E.LinkArmPlaceB
import FV.E2E.LinkPlaceBWitness

/-!
# A linked test system with slotted, returning program callees (SEM1 #537)

Almost every SEM1 witness so far uses `Lu` (`LinkArmUProgWitness`), whose program callee never
returns (it calls the raising `throw`), or `¬ NeedSlots`; that is how #694 slipped through. This
system is the witness system for the slot-byte statements from now on: `P = {f, h, r}` compiled
by the compiler's pipeline (`LinkInput`, spill fallback), loaded at `0x10000`, `0x20000`,
`0x30000`, no base externs (`closedBase`):

* `h n = n`: stores `n` in its 8-byte slot and loads it back (a written slot);
* `r n = n + slot`: loads its 8-byte slot without writing it (an unwritten slot read);
* `f n = r (h n)`: no slot, calls `h` then `r`.

`h` and `r` have the same frame, so `r`'s slot is the stack bytes `h` left behind: the machine
computes `f 41 = 41 + 41 = 82`. The CLIF run gives the same result exactly when the slot-byte
table is the machine's (entry `k` = the memory at the `k`-th placed activation with slots):
`iniT` has `41` at `r`'s slot in entry `2`.

Checked (`#guard`, on a computable mirror of the linked machine `machC`, depth `1`): the machine
returns `82` to the entry's return address with the entry's `sp`, calling `h` then `r` at the
body `sp` `0xFFF40`, and `iniT` is the machine's table on both callees' slot bytes. Theorems:

* `Lsl_ok`, `needSlots`: `LinkSys.Ok` (`okB`, `native_decide`) and `NeedSlots`;
* `run_f`: the whole-program CLIF run from `f`'s entry `cs0` on `41` (placed at `0x100000` with
  `iniT`) returns `82` = the machine's result; with the zero table it returns `41` (`run_f_zero`);
* **`nextAdv_leave_f`**: `NextAdv cs0.mem.leave cm' 2`, the count of the machine's placed
  activations with slots (`ThmPRBRL`'s corrected conjunct holds, `CountPRB`'s `e = 2`);
* `not_nextAdv_f`: `NextAdv cs0.mem cm' e` fails for every `e` (#694 on a real program).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck

def srcF : String := "function %f(i64) -> i64 system_v {
    fn0 = colocated %h(i64) -> i64 system_v
    fn1 = colocated %r(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    v2 = call fn1(v1)
    return v2
}
"

def srcH : String := "function %h(i64) -> i64 system_v {
    ss0 = explicit_slot 8
block0(v0: i64):
    v1 = stack_addr.i64 ss0
    store.i64 notrap aligned v0, v1
    v2 = load.i64 notrap aligned v1
    return v2
}
"

def srcR : String := "function %r(i64) -> i64 system_v {
    ss0 = explicit_slot 8
block0(v0: i64):
    v1 = stack_addr.i64 ss0
    v2 = load.i64 notrap aligned v1
    v3 = iadd v0, v2
    return v3
}
"

/-- The input: `f`, `h`, `r`, compiled by the compiler's pipeline. -/
def I : LinkInput where
  funcs := [{ clif := srcF, ra := "{}" }, { clif := srcH, ra := "{}" }, { clif := srcR, ra := "{}" }]
  addrs := [("f", 0x10000), ("h", 0x20000), ("r", 0x30000)]
  syms := []
  raStar := 0x40000
  D := 4096
  fallback := true

theorem okB_true : okB I = true := by native_decide

/-- The code image (independent of `F`). -/
def world : BitVec 64 → Prop := (LinkSys.ofInput I closedBase fun _ => False).Img

/-- **The linked system**, with its default callee runs. -/
def L0 : LinkSys := LinkSys.ofInput I closedBase world

def Lsl : LinkSys := L0.std

theorem noTls : ∀ g ∈ (progOf I.results).funcs, hasTls g = false := by
  have h : (progOf I.results).funcs.all (fun g => !hasTls g) = true := by native_decide
  intro g hg
  simpa using List.all_eq_true.mp h g hg

theorem L0_ok : L0.Ok := okB_sound okB_true (baseOk_closed noTls) fun _ h => h

theorem Lsl_ok : Lsl.Ok := L0_ok.withCrun _

instance : Lsl.CrunOk := L0.crunOk_std L0_ok

def fF : Clif.Function := (Lsl.P.func? "f").getD default
def fH : Clif.Function := (Lsl.P.func? "h").getD default
def fR : Clif.Function := (Lsl.P.func? "r").getD default

def funcsB : Bool :=
  Lsl.P.func? "f" == some fF && Lsl.P.func? "h" == some fH && Lsl.P.func? "r" == some fR &&
    Lsl.P.funcs == [fF, fH, fR] && fF.name == "f" && !fH.slots.isEmpty && !fR.slots.isEmpty &&
    fF.slots.isEmpty &&
    (fF.externs.map (·.2)).any (fun e => Lsl.P.func? e.name == some fH)

theorem funcsB_true : funcsB = true := by native_decide

theorem func?_f : Lsl.P.func? "f" = some fF := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.1.1.1
theorem func?_h : Lsl.P.func? "h" = some fH := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.1.1.2
theorem funcs_eq : Lsl.P.funcs = [fF, fH, fR] := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1.1.2
theorem fH_slots : fH.slots ≠ [] := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h
  have h1 := h.1.1.1.2
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h1; exact h1
theorem fF_slots : fF.slots.isEmpty = true := by
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2

/-- **The system needs the slot-placement oracle**: `f` declares `h`, which has a slot. -/
theorem needSlots : Lsl.NeedSlots := by
  refine ⟨fF, by rw [funcs_eq]; simp, fH, .inr (.inl ?_), fH_slots⟩
  have h := funcsB_true; simp only [funcsB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, he'⟩ := List.any_eq_true.mp h.2
  exact ⟨e, he, by simpa using he'⟩

/-! ## A computable mirror of the linked machine (checks only) -/

/-- `insnAt` by search. -/
def insnAtC (fa : FnAsm) (base pc : BitVec 64) : Option Insn :=
  let l := fa.lines.toList
  (List.range l.length).findSome? fun j => match l[j]? with
    | some (Line.ins i _) => if base + BitVec.ofNat 64 (lineOffset l j) = pc then some i else none
    | _ => none

/-- `ArmStepX` for a non-call instruction. -/
def stepC (fa : FnAsm) (s : Arm.ArmState) : Arm.ArmState :=
  let pc := Arm.r .PC s
  match insnAtC fa (progBase s) pc with
  | some (.adrpGot rd n) =>
    Arm.w .PC (pc + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (Lsl.Xb.sym n 0) s)
  | some (.ldrGotLo12 _ _ _) => Arm.w .PC (pc + 4) s
  | some (.adrp rd n off) =>
    Arm.w .PC (pc + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (Lsl.Xb.sym n off) s)
  | some (.addLo12 _ _ _ _) => Arm.w .PC (pc + 4) s
  | _ => Arm.stepi s

def retOfB (s t : Arm.ArmState) : Bool :=
  Arm.r .PC t == Arm.r .PC s + 4 && (match Arm.r .ERR t with | .None => true | _ => false) &&
    spv t == spv s

/-- **The linked machine** (`mach depth g` with `linkedCall`, searching `fuel` steps): the
return state, and the program calls `(callee, state at the call)` in entry order. -/
partial def machC (depth fuel : Nat) (g : Clif.Function) (s0 : Arm.ArmState) :
    Option (Nat × Arm.ArmState) × List (String × Arm.ArmState) :=
  let a := Lsl.A g
  let rec loop (k : Nat) (t : Arm.ArmState) (log : List (String × Arm.ArmState)) :
      Option (Nat × Arm.ArmState) × List (String × Arm.ArmState) :=
    if retOfB s0 t then (some (k, t), log)
    else if k ≥ fuel then (none, log)
    else match insnAtC a.fa (progBase t) (Arm.r .PC t) with
      | some (.bl n) => match Lsl.P.func? n with
        | some h =>
          if depth = 0 then loop (k + 1) (junkAt t) log else
          match machC (depth - 1) fuel h t with
          | (some (_, v), log') => loop (k + 1) (Arm.set_program v t.program) (log ++ [(n, t)] ++ log')
          | (none, log') => loop (k + 1) (junkAt t) (log ++ [(n, t)] ++ log')
        | none => loop (k + 1) (Arm.w .PC (Arm.r .PC t + 4) t) log
      | _ => loop (k + 1) (stepC a.fa t) log
  loop 0 (enterAt a s0) []

/-- The caller's state: `x0 = 41`, `sp = 0x100000`, the code image, before `raStar`. -/
def sEntry : Arm.ArmState :=
  Arm.w .PC (Lsl.raStar - 4) (Arm.w (.GPR 0#5) 41#64 (Arm.w (.GPR 31#5) 0x100000#64
    (setMem Arm.ArmState.default Lsl.imgMem)))

def resM := machC 1 2000 fF sEntry

/-- The memory at the `k`-th placed activation with slots (`1`: `h`, `2`: `r`). -/
def callSt (k : Nat) : Arm.ArmState := ((resM.2[k - 1]?).map (·.2)).getD sEntry

/-- `r`'s slot address at its call: the body `sp` plus the slot base. -/
def slotR : Nat := 0x100000 - 192 - 208 + 32

/-- **The byte table**: entry `2` (`r`) holds `h`'s leftover `41` at `r`'s slot. -/
def iniT : Clif.SlotInit := { bytes := fun k a => if k = 2 ∧ a = slotR then 41#8 else 0#8 }

-- The machine returns `82` to the return address with the entry's `sp`.
#guard match resM.1 with
  | some (_, t) => Arm.r (.GPR 0#5) t == 82#64 && spv t == 0x100000#64
  | none => false
-- It calls `h` then `r`, both at the body `sp` of `f` (`0x100000 - 192`).
#guard resM.2.map (fun p => (p.1, spv p.2)) == [("h", 0xFFF40#64), ("r", 0xFFF40#64)]
-- `iniT` is the machine's table on both callees' slot bytes.
#guard [(1, fH), (2, fR)].all fun (k, h) =>
  let c := spv (callSt k) - BitVec.ofNat 64 (frameDrop (Lsl.A h).af) +
    BitVec.ofNat 64 (Lsl.A h).af.slotBase
  (List.range 8).all fun i =>
    (callSt k).mem (c + BitVec.ofNat 64 i) == iniT.bytes k (c + BitVec.ofNat 64 i).toNat

/-! ## The CLIF side -/

deriving instance Inhabited for Clif.Frame
deriving instance Inhabited for Clif.State

/-- The caller's memory: placed at `0x100000` with the table `ini`, counter `0`. -/
def memS (ini : Clif.SlotInit) : Clif.Mem := { place := some ⟨[0x100000#64], Lsl.frames, some ini⟩ }

def csOf (ini : Clif.SlotInit) : Clif.State := match Clif.initState Lsl.P "f" [⟨.i64, 41#64⟩] (memS ini) with
  | .ok cs => cs
  | _ => default

def runOf (ini : Clif.SlotInit) : Clif.Outcome := Lsl.crun 100 (csOf ini)

def memOf (ini : Clif.SlotInit) : Clif.Mem := match runOf ini with
  | .returned _ m => m
  | _ => {}

/-- `f`'s entry on `41` from `memS iniT`. -/
def cs0 : Clif.State := csOf iniT

def checkB : Bool :=
  (match Clif.initState Lsl.P "f" [⟨.i64, 41#64⟩] (memS iniT) with
    | .ok _ => true
    | _ => false) &&
  (match runOf iniT with
    | .returned [v] m => v.bits.toNat == 82 && (m.place.map fun pl => (pl.sps, pl.init.map (·.next))) ==
        some ([0x100000#64], some 2)
    | _ => false) &&
  (match runOf { bytes := fun _ _ => 0#8 } with
    | .returned [v] _ => v.bits.toNat == 41
    | _ => false) &&
  (cs0.mem.place.map (·.sps)) == some [0xFFF40#64, 0x100000#64]

theorem checkB_true : checkB = true := by native_decide

theorem init_ok : Clif.initState Lsl.P "f" [⟨.i64, 41#64⟩] (memS iniT) = .ok cs0 := by
  have h := checkB_true
  simp only [checkB, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  unfold cs0 csOf
  split at h1 <;> rename_i hi
  · rw [hi]
  · cases h1

/-- **The CLIF run returns the machine's `82`** (and `cm'` is placed with counter `2`). -/
theorem run_f : ∃ v, Lsl.crun 100 cs0 = .returned [v] (memOf iniT) ∧ v.bits.toNat = 82 ∧
    ((memOf iniT).place.map fun pl => (pl.sps, pl.init.map (·.next))) = some ([0x100000#64], some 2) := by
  have h := checkB_true
  simp only [checkB, Bool.and_eq_true] at h
  have h2 := h.1.1.2
  unfold memOf
  revert h2
  show (match runOf iniT with
    | .returned [v] m => v.bits.toNat == 82 && (m.place.map fun pl => (pl.sps, pl.init.map (·.next))) ==
        some ([0x100000#64], some 2)
    | _ => false) = true → _
  unfold runOf
  intro h2
  split at h2
  · rename_i v m hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨v, by rw [show cs0 = csOf iniT from rfl, hr], h2.1, by rw [hr]; exact h2.2⟩
  · cases h2

/-- With the zero table the CLIF run returns `41`, not the machine's `82`: the table must be the
machine's. -/
theorem run_f_zero : ∃ v m, runOf { bytes := fun _ _ => 0#8 } = .returned [v] m ∧ v.bits.toNat = 41 := by
  have h := checkB_true
  simp only [checkB, Bool.and_eq_true] at h
  have h3 := h.1.2
  split at h3
  · rename_i v m hr
    exact ⟨v, m, hr, by simpa using h3⟩
  · cases h3

theorem placeAtB_memS : Lsl.PlaceAtB (memS iniT) 0x100000#64 iniT := ⟨[], rfl⟩

/-- **`ThmPRBRL`'s corrected conjunct on a slotted program**: the advance from the popped entry is
`2`, the machine's two placed activations with slots. -/
theorem nextAdv_leave_f : Clif.NextAdv cs0.mem.leave (memOf iniT) 2 := by
  obtain ⟨v, hr, -, hp⟩ := run_f
  obtain ⟨e, he⟩ := Clif.runsOf_nextAdv (LinkSys.CrunOk.runs (L := Lsl) 100) Lsl_ok.free
    (Clif.envAdv_of_keepsPlace LinkPlaceBWitness.keeps_empty) init_ok hr
  have hl := Lsl.initState_leave_nextAdv func?_f init_ok placeAtB_memS
  simp only [fF_slots, ↓reduceIte] at hl
  have hm : (memS iniT).place = some ⟨[0x100000#64], Lsl.frames, some iniT⟩ := rfl
  have he2 : e = 2 := by
    have := he _ _ hm rfl
    rw [this] at hp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Clif.SlotInit.adv] at hp
    have := hp.2
    simp only [iniT] at this
    omega
  subst he2
  simpa using Clif.NextAdv.cancel hl he hm rfl (Nat.zero_le 2)

/-- **#694 on a slotted program**: no advance from the entry memory itself. -/
theorem not_nextAdv_f (e : Nat) : ¬ Clif.NextAdv cs0.mem (memOf iniT) e := by
  obtain ⟨-, -, -, hp⟩ := run_f
  have hpl := Lsl.initState_place func?_f init_ok (sps := []) (c := 0x100000#64) rfl
  intro h
  have h1 := h _ _ hpl rfl
  rw [h1] at hp
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hp
  exact absurd hp.1.2 (by simp)

end E2E.LinkSlotSysWitness
