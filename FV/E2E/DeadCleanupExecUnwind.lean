import FV.E2E.DeadCleanupExecTrap
import FV.E2E.LinkArmUEnv
import FV.E2E.LinkArmUEnvCall
import FV.Link.EhCheck

/-!
# The executable machine with unwinding (S10g, #404)

`DeadCleanupExecBytes.step I B file` (the processor on the executable's words, calls of code
outside the program and the TLS sequence by the base hooks) with **phase 2 of the unwinder on the
executable's own tables**:

* `unwFrame file ra obj t`: one frame of phase 2 for the frame whose return address is `ra` (its
  call at `ra - 4`), the unwinder having restored the frame's state `t` at that call: libunwind's
  lookup in `file` (`Link.EhCheck.unwTables`, at `ra - 1` as libunwind looks up a caller's frame),
  then Rust's personality and the frame's row (`Unw.unwindAt`: install the landing pad, unwind the
  frame, or stop). No FDE: the unwinder stops.
* `Walk I file ra obj t r`: **the frame walk** from that frame ends in `r`: after a frame unwound
  by its row (`Continues`) whose restored return address designates a frame of the program's code
  (`img I (ra' - 1)`, `NextFrame`), the walk continues with that frame; otherwise the frame's
  result is the walk's (a landing pad, an error, or — the return address outside the program's
  code — the exception leaving the program: an AAPCS64 return to the outside caller, the
  exception object in x0). `Walk` is deterministic (`walk_det`).
* `stepU I B Ub file`: **the executable machine with unwinding**: `step`, but at a call of code
  outside the program whose callee raises (`Ub`, the base environment's raising callees, as in
  `LinkSysU.Ub`: the callee and every frame below it unwound, `t` the state at our call as the
  unwinder restored it) the whole frame walk in one step (`walk`: the walk's result; without one,
  an error). A call of a function of the program is executed from the file's words: its raise
  happens at a deeper call.

Design: a flat machine has no activation stack; the frame walk is driven by the return addresses
the frames' rows restore, as libunwind's is. Keeping the walk one machine step (an inductive
relation, its unique result) lets the simulation compose frame by frame across the nested
machine's activations (`Pending`: the walk the executable's raising step performs is at a given
frame).

The simulation of the linked machine with unwinding (`LinkSysU.machU`) is `act_simU`, under the
per-state facts `RunOkU` of the model's run (`StepOkU`: `StepOk` on the machine with unwinding and
the restored frames' save slots off the relocated bytes; the return after an unwound frame);
`exec_of_modelU` transfers `ArmRefinesU` to `ExecRefinesU`.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The machine -/

section Machine

variable (I : LinkInput) (B : BaseEnv) (Ub : Unw.UnwHooks) (file : ByteArray)

/-- **One frame of phase 2 on the executable's tables**: the frame whose return address is `ra`
(its call at `ra - 4`), restored at that call in `t`, the exception object `obj`: the lookup in
`file` at `ra - 1`, then the personality and the frame's row (`Unw.unwindAt`). -/
def unwFrame (ra obj : BitVec 64) (t : Arm.ArmState) : Arm.ArmState :=
  match Link.EhCheck.unwTables file (ra - 1).toNat with
  | some (start, T) => Unw.unwindAt T (BitVec.ofNat 64 start) (ra - 4) obj t
  | none => Unw.stop "unwind: no FDE" t

/-- The frame of return address `ra` restored in `t` is unwound by its row: the personality
continues and the row's CFA rule applies. -/
def Continues (ra : BitVec 64) (t : Arm.ArmState) : Prop :=
  ∃ start T, Link.EhCheck.unwTables file (ra - 1).toNat = some (start, T) ∧
    Unw.personality T.lsda (ra - 4 + 4 - 1 - BitVec.ofNat 64 start).toNat = .continue ∧
    (Unw.restore (Unw.rowAt T.cie T.fde (ra - 4 + 4 - 1 - BitVec.ofNat 64 start).toNat) t).isSome

/-- The walk continues after the frame of `ra`: the frame was unwound and its restored return
address designates a frame of the program's code. -/
def NextFrame (ra obj : BitVec 64) (t : Arm.ArmState) : Prop :=
  Continues file ra t ∧ img I (Arm.r .PC (unwFrame file ra obj t) - 1)

/-- **The frame walk** from the frame of return address `ra` restored in `t` ends in `r`. -/
inductive Walk : BitVec 64 → BitVec 64 → Arm.ArmState → Arm.ArmState → Prop
  | last {ra obj : BitVec 64} {t : Arm.ArmState} : ¬ NextFrame I file ra obj t →
      Walk ra obj t (unwFrame file ra obj t)
  | next {ra obj : BitVec 64} {t r : Arm.ArmState} : NextFrame I file ra obj t →
      Walk (Arm.r .PC (unwFrame file ra obj t)) obj (unwFrame file ra obj t) r → Walk ra obj t r

open Classical in
/-- The frame walk's result (an error if the walk does not end). -/
noncomputable def walk (ra obj : BitVec 64) (t : Arm.ArmState) : Arm.ArmState :=
  if h : ∃ r, Walk I file ra obj t r then h.choose else Unw.stop "unwind: unbounded" t

/-- The raise of the callee outside the program called at `s` (`Ub`), if any. -/
noncomputable def raiseAt (s : Arm.ArmState) : Option (BitVec 64 × Arm.ArmState) :=
  match siteAt I (Arm.r .PC s) with
  | some (.extCall n) => Ub.raise (some n) s
  | some .blr =>
    if ((blrTarget s).bind (symCallee (sys I B).Xb (prog I))).isSome then none
    else Ub.raise none s
  | _ => none

/-- **The executable machine with unwinding**: `step`, but a call of code outside the program
whose callee raises runs the frame walk on the executable's tables. -/
noncomputable def stepU (s : Arm.ArmState) : Arm.ArmState :=
  match raiseAt I B Ub s with
  | some (obj, t) => walk I file (Arm.r .PC s + 4) obj t
  | none => step I B file s

/-- **The walk the step at `e` performs is at the frame of return address `ra` restored in
`t`**: every end of the walk from there is the step's result. -/
def Pending (e : Arm.ArmState) (ra obj : BitVec 64) (t : Arm.ArmState) : Prop :=
  ∀ r, Walk I file ra obj t r → stepU I B Ub file e = r

end Machine

/-! ## The frame walk -/

section WalkLemmas

variable {I : LinkInput} {B : BaseEnv} {Ub : Unw.UnwHooks} {file : ByteArray}

/-- **The frame walk is deterministic.** -/
theorem walk_det {ra obj : BitVec 64} {t r : Arm.ArmState} (h : Walk I file ra obj t r) :
    ∀ {r'}, Walk I file ra obj t r' → r = r' := by
  induction h with
  | last hn =>
    intro r' h'
    cases h' with
    | last _ => rfl
    | next hx _ => exact absurd hx hn
  | next hx _ ih =>
    intro r' h'
    cases h' with
    | last hn => exact absurd hx hn
    | next _ h2 => exact ih h2

theorem walk_eq {ra obj : BitVec 64} {t r : Arm.ArmState} (h : Walk I file ra obj t r) :
    walk I file ra obj t = r := by
  have hex : ∃ r, Walk I file ra obj t r := ⟨r, h⟩
  simp only [walk, hex, ↓reduceDIte]
  exact walk_det (Classical.choose_spec hex) h

theorem stepU_of_none {e : Arm.ArmState} (h : raiseAt I B Ub e = none) :
    stepU I B Ub file e = step I B file e := by
  simp only [stepU, h]

/-- At a raising call the walk is at the frame of the call. -/
theorem pending_raise {e : Arm.ArmState} {obj : BitVec 64} {t : Arm.ArmState}
    (h : raiseAt I B Ub e = some (obj, t)) : Pending I B Ub file e (Arm.r .PC e + 4) obj t := by
  intro r hw
  simp only [stepU, h]
  exact walk_eq hw

/-- The walk moves on to the next frame. -/
theorem Pending.next {e : Arm.ArmState} {ra obj : BitVec 64} {t : Arm.ArmState}
    (h : Pending I B Ub file e ra obj t) (hn : NextFrame I file ra obj t) :
    Pending I B Ub file e (Arm.r .PC (unwFrame file ra obj t)) obj (unwFrame file ra obj t) :=
  fun r hw => h r (.next hn hw)

/-- The walk ends at a frame that does not continue to a frame of the program. -/
theorem Pending.last {e : Arm.ArmState} {ra obj : BitVec 64} {t : Arm.ArmState}
    (h : Pending I B Ub file e ra obj t) (hn : ¬ NextFrame I file ra obj t) :
    stepU I B Ub file e = unwFrame file ra obj t :=
  h _ (.last hn)

end WalkLemmas

end E2E.DeadCleanupExecBytes

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The linked machine with unwinding of the input -/

/-- **The linked program with unwinding of the input** with the raising callees (and CLIF base)
of `U`, no address outside the world (`sys`): its machine is that of every linked program with
unwinding of the input with `U`'s raising callees (`machU_uSys`). -/
def uSys (I : LinkInput) (B : BaseEnv) (U : LinkSysU) : LinkSysU := { U with toLinkSys := sys I B }

section Nested

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem layer_uSys {U : LinkSysU} {F : BitVec 64 → Prop}
    (hU : U.toLinkSys = LinkSys.ofInputCleanup I B F) : ∀ M, U.layer M = (uSys I B U).layer M := by
  obtain ⟨L0, Ub, envX, XRb, crunX⟩ := U
  change L0 = _ at hU
  subst hU
  intro M
  induction M with
  | zero => rfl
  | succ M ih =>
    unfold LinkSysU.layer
    rw [ih]
    rfl

/-- The machine of a linked program with unwinding of the input is `uSys`'s. -/
theorem machU_uSys {U : LinkSysU} {F : BitVec 64 → Prop}
    (hU : U.toLinkSys = LinkSys.ofInputCleanup I B F) (M : Nat) (g : Clif.Function) :
    U.machU M g = (uSys I B U).machU M g := by
  simp only [LinkSysU.machU, LinkSysU.hooksU, LinkSysU.UU, layer_uSys hU M]
  obtain ⟨L0, Ub, envX, XRb, crunX⟩ := U
  change L0 = _ at hU
  subst hU
  rfl

theorem armStepU_nocall {X : ExtSem} {H : ArmHooks} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {fa : FnAsm} {s : Arm.ArmState} {i : Insn}
    (hi : insnAt fa (progBase s) (Arm.r .PC s) = some i) (h1 : ∀ n, i ≠ .bl n)
    (h2 : ∀ x, i ≠ .blr x) : Unw.ArmStepU X H U T fa s = ArmStepX X H fa s := by
  unfold Unw.ArmStepU
  simp only [hi]
  cases i <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _)

theorem armStepX_tls {X : ExtSem} {H H' : ArmHooks} {fa : FnAsm} {s : Arm.ArmState} {i : Insn}
    (hi : insnAt fa (progBase s) (Arm.r .PC s) = some i) (h1 : ∀ n, i ≠ .bl n)
    (h2 : ∀ x, i ≠ .blr x) (h : H.tls = H'.tls) : ArmStepX X H fa s = ArmStepX X H' fa s := by
  simp only [ArmStepX, hi]
  cases i <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _) | rw [h]

/-- At an instruction that is no call the machine with unwinding steps as the linked machine. -/
theorem machU_nocall (U : LinkSysU) {M : Nat} {g : Clif.Function} {m : Arm.ArmState} {i : Insn}
    (hi : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some i) (h1 : ∀ n, i ≠ .bl n)
    (h2 : ∀ x, i ≠ .blr x) : (uSys I B U).machU M g m = (sys I B).mach M g m := by
  show Unw.ArmStepU (sys I B).Xb ((uSys I B U).hooksU M) ((uSys I B U).UU M) (art I g).tables
    (art I g).fa m = ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m
  rw [armStepU_nocall hi h1 h2]
  exact armStepX_tls hi h1 h2 (by rw [LinkSysU.hooksU_tls, hooks_tls]; rfl)

/-- **A call of code outside the program**: the callee's raise (`Ub`) runs the frame's phase 2,
else the base hook. -/
theorem machU_base (U : LinkSysU) {M : Nat} {g : Clif.Function} {m : Arm.ArmState} {i : Insn}
    {d : Option String} (hi : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some i)
    (hd : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) :
    (uSys I B U).machU M g m = match U.Ub.raise d m with
      | some (obj, t) => Unw.unwindAt (art I g).tables (progBase m) (Arm.r .PC m) obj t
      | none => B.hooks.call d m := by
  have hb : (uSys I B U).BaseDest d := by
    rcases hd with ⟨n, -, hn, rfl⟩ | ⟨x, -, -, rfl⟩
    · exact .inr ⟨n, rfl, hn⟩
    · exact .inl rfl
  have hn : d = none → (blrTarget m).bind (symCallee (uSys I B U).Xb (uSys I B U).P) = none := by
    rintro rfl
    rcases hd with ⟨n, -, -, h⟩ | ⟨x, -, h, -⟩
    · cases h
    · exact h
  have hr := (uSys I B U).UU_base (M := M) hb m hn
  have hc := (uSys I B U).hooksU_base (M := M) hb m hn
  show Unw.ArmStepU (sys I B).Xb ((uSys I B U).hooksU M) ((uSys I B U).UU M) (art I g).tables
    (art I g).fa m = _
  unfold Unw.ArmStepU
  rcases hd with ⟨n, rfl, -, rfl⟩ | ⟨x, rfl, -, rfl⟩
  · simp only [hi, hr, hc]; rfl
  · simp only [hi, hr, hc]; rfl

/-- **A call of a function `h` of the program**: its raise (the callee's run leaving its frame by
unwinding, `praiseU`) runs the frame's phase 2, else the linked call. -/
theorem machU_prog (U : LinkSysU) {M : Nat} {g h : Clif.Function} {m : Arm.ArmState}
    (hc : CallsAt I B g m h) :
    (uSys I B U).machU M g m = match (uSys I B U).praiseU M h m with
      | some (obj, t) => Unw.unwindAt (art I g).tables (progBase m) (Arm.r .PC m) obj t
      | none => (uSys I B U).pcallU M h m := by
  show Unw.ArmStepU (sys I B).Xb ((uSys I B U).hooksU M) ((uSys I B U).UU M) (art I g).tables
    (art I g).fa m = _
  unfold Unw.ArmStepU
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
  · simp only [hins, (uSys I B U).UU_some (M := M) (u := m) hn,
      (uSys I B U).hooksU_some (M := M) hn m]
    rfl
  · simp only [hins, (uSys I B U).UU_none (M := M) hcal, (uSys I B U).hooksU_none (M := M) hcal]
    rfl

end Nested

/-! ## One frame of phase 2 on simulated states -/

section FrameSim

variable {I : LinkInput} {B : BaseEnv} {Ub : Unw.UnwHooks} {file : ByteArray}

variable (I) in
/-- **The save slots of the frame row at the call `pc` (function start `start`, tables `T`) in
`t` are no relocated instruction bytes**: what unwinding the frame reads. -/
def RestoreOk (T : Unw.FnTables) (start pc : BitVec 64) (t : Arm.ArmState) : Prop :=
  ∀ cfa, (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat).cfa? t = some cfa →
    ∀ p ∈ (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat).saved, ∀ k < 8,
      ¬ DeadCleanupBinCheck.RelocAt I (cfa + BitVec.ofInt 64 p.2 + BitVec.ofNat 64 k)

theorem regVal?_sim {m e : Arm.ArmState} (h : Sim I m e) (r : Nat) :
    Unw.regVal? e r = Unw.regVal? m r := by
  simp only [Unw.regVal?, h.1]

theorem cfa?_sim {m e : Arm.ArmState} (h : Sim I m e) (row : Unw.Row) :
    row.cfa? e = row.cfa? m := by
  simp only [Unw.Row.cfa?, regVal?_sim h]

theorem setReg_sim {m e : Arm.ArmState} (h : Sim I m e) (d : Nat) (v : BitVec 64) :
    Sim I (Unw.setReg d v m) (Unw.setReg d v e) := by
  unfold Unw.setReg
  split
  · exact sim_w h _ _
  · split
    · exact sim_w h _ _
    · exact h

theorem restoreFold_sim {m e : Arm.ArmState} (h : Sim I m e) (cfa : BitVec 64) :
    ∀ L : List (Nat × Int), (∀ p ∈ L, Unw.ld64 (cfa + BitVec.ofInt 64 p.2) m =
      Unw.ld64 (cfa + BitVec.ofInt 64 p.2) e) →
    Sim I (Unw.restoreFold cfa m L) (Unw.restoreFold cfa e L)
  | [], _ => h
  | (d, off) :: L, hL => by
    have ih := restoreFold_sim h cfa L fun p hp => hL p (List.mem_cons_of_mem _ hp)
    simp only [Unw.restoreFold, List.foldr_cons] at ih ⊢
    rw [hL (d, off) List.mem_cons_self]
    exact setReg_sim ih d _

/-- **Unwinding a frame keeps the simulation** when its save slots are no relocated bytes. -/
theorem restore_sim {m e : Arm.ArmState} (h : Sim I m e) {row : Unw.Row}
    (hr : ∀ cfa, row.cfa? m = some cfa → ∀ p ∈ row.saved, ∀ k < 8,
      ¬ DeadCleanupBinCheck.RelocAt I (cfa + BitVec.ofInt 64 p.2 + BitVec.ofNat 64 k)) :
    Option.Rel (Sim I) (Unw.restore row m) (Unw.restore row e) := by
  unfold Unw.restore
  rw [cfa?_sim h]
  cases hc : row.cfa? m with
  | none => exact .none
  | some cfa =>
    refine .some ?_
    have hf := restoreFold_sim h cfa row.saved fun p hp =>
      rmb_congr 8 _ fun k hk => (h.2 _ (hr cfa hc p hp k hk)).symm
    show Sim I (Arm.w .PC (Arm.r (.GPR 30#5) (Unw.restoreFold cfa m row.saved))
        (Arm.w (.GPR 31#5) cfa (Unw.restoreFold cfa m row.saved)))
      (Arm.w .PC (Arm.r (.GPR 30#5) (Unw.restoreFold cfa e row.saved))
        (Arm.w (.GPR 31#5) cfa (Unw.restoreFold cfa e row.saved)))
    rw [hf.1]
    exact sim_w (sim_w hf _ _) _ _

theorem restore_isSome_sim {m e : Arm.ArmState} (h : Sim I m e) (row : Unw.Row) :
    (Unw.restore row e).isSome = (Unw.restore row m).isSome := by
  simp only [Unw.restore, cfa?_sim h, Option.isSome_map]

/-- **Phase 2 at a frame keeps the simulation** when its save slots are no relocated bytes. -/
theorem unwindAt_sim {m e : Arm.ArmState} (h : Sim I m e) {T : Unw.FnTables}
    {start pc obj : BitVec 64} (hr : RestoreOk I T start pc m) :
    Sim I (Unw.unwindAt T start pc obj m) (Unw.unwindAt T start pc obj e) := by
  unfold Unw.unwindAt
  dsimp only
  split
  · exact sim_w (sim_w (sim_w h _ _) _ _) _ _
  · have hrs := restore_sim h (row := Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) hr
    revert hrs
    generalize Unw.restore (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) m = a
    generalize Unw.restore (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) e = b
    intro hrs
    cases hrs with
    | none => exact sim_w h _ _
    | some hs => exact sim_w hs _ _
  · exact sim_w h _ _

/-- A frame whose personality continues and whose phase 2 ends without error is unwound by its
row, the exception object in x0. -/
theorem unwindAt_continues {T : Unw.FnTables} {start pc obj : BitVec 64} {t : Arm.ArmState}
    (hp : Unw.personality T.lsda (pc + 4 - 1 - start).toNat = .continue)
    (he : Arm.r .ERR (Unw.unwindAt T start pc obj t) = .None) :
    (Unw.restore (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) t).isSome ∧
      xreg 0 (Unw.unwindAt T start pc obj t) = obj := by
  simp only [Unw.unwindAt, hp] at he ⊢
  cases hr : Unw.restore (Unw.rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) t with
  | none =>
    rw [hr] at he
    simp [Unw.stop, Arm.r_of_w_same] at he
  | some t' =>
    simp only [Option.isSome_some, xreg, true_and]
    exact Arm.r_of_w_same

end FrameSim

end E2E.DeadCleanupExecBytes

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The hypotheses -/

/-- **The base environment's raising callees do not read the relocated instruction bytes nor
the program field** (`Sim` before gives the same exception object and `Sim` after): `HooksSim`
for `Unw.UnwHooks`, the contract the executable machine with unwinding adds. -/
structure UnwSim (I : LinkInput) (Ub : Unw.UnwHooks) : Prop where
  raise : ∀ d m e obj t, Sim I m e → Ub.raise d m = some (obj, t) →
    ∃ t', Ub.raise d e = some (obj, t') ∧ Sim I t t'
  none : ∀ d m e, Sim I m e → Ub.raise d m = none → Ub.raise d e = none

/-- No raising callee meets `UnwSim`. -/
theorem unwSim_none (I : LinkInput) : UnwSim I Unw.UnwHooks.none :=
  ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ => rfl⟩

/-- **The executable's unwind tables are the compiled functions'**: libunwind's lookup in
`file` at every pc of a compiled function gives its address and tables
(`Link.DeadCleanup.compileExeU_tables`). -/
def TabsOk (I : LinkInput) (file : ByteArray) : Prop :=
  ∀ g ∈ (prog I).funcs, ∀ pc, (art I g).base.toNat ≤ pc →
    pc < (art I g).base.toNat + (art I g).fb.size →
    Link.EhCheck.unwTables file pc = some ((art I g).base.toNat, (art I g).tables)

section Defs

variable (I : LinkInput) (B : BaseEnv) (file : ByteArray) (U : LinkSysU)

/-- **The states of the activation of `g` at depth `M` entered at `c` of the machine with
unwinding** before its return, and of the activations nested through its calls whose step ends
without error (`ReachN` with the activation's entry: the last three indices are the state's
activation's depth, function and entry, and the state). -/
inductive ReachU : Nat → Clif.Function → Arm.ArmState → Nat → Clif.Function → Arm.ArmState →
    Arm.ArmState → Prop
  | act {M g c k} : (∀ j ≤ k, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c)) →
      ReachU M g c M g c (runX ((uSys I B U).machU M g) k c)
  | nest {M g c k h M' g' c' t} :
      (∀ j ≤ k, ¬ Returned (art I g) c (runX ((uSys I B U).machU (M + 1) g) j c)) →
      CallsAt I B g (runX ((uSys I B U).machU (M + 1) g) k c) h →
      Arm.r .ERR (runX ((uSys I B U).machU (M + 1) g) (k + 1) c) = .None →
      ReachU M h (enterAt (art I h) (runX ((uSys I B U).machU (M + 1) g) k c)) M' g' c' t →
      ReachU (M + 1) g c M' g' c' t

/-- **What the lockstep with unwinding needs of a model state** `m` of an activation of `g` at
depth `M`: `StepOk` with D1 on the machine with unwinding, and the save slots of `g`'s frame row
at a raising call no relocated instruction bytes (what the frame's phase 2 reads). -/
structure StepOkU (M : Nat) (g : Clif.Function) (m : Arm.ArmState) : Prop where
  err : Arm.r .ERR m = .None
  program : m.program = (art I g).fb.program (art I g).base
  site : ∃ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i ∧
    siteAt I (Arm.r .PC m) = some (siteOf (prog I) i) ∧ (i.reloc? = none ∨ i.hooked = true)
  cf : ∀ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) →
    Arm.r .PC ((uSys I B U).machU M g m) = wAt (art I g) (rl.offset + 4) →
    Arm.r .PC m = wAt (art I g) rl.offset
  insn : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ∀ e, Sim I m e → Sim I (Arm.exec_inst a m) (Arm.exec_inst a e)
  call : ∀ d e, ((∃ n, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.bl n) ∧
        (prog I).func? n = none ∧ d = some n) ∨
      ((∃ x, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x)) ∧
        (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) →
    Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e)
  tls : ∀ tmp rn n e, insnAt (art I g).fa (art I g).base (Arm.r .PC m) =
      some (.ldrTlsDescLo12 tmp rn n) →
    Sim I m e → Sim I (B.hooks.tls n tmp m) (B.hooks.tls n tmp e)
  got : ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC m = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (pageOf G - pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ E2E.DeadCleanupBinCheck.RelocAt I (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    m.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0
  blr : ∀ x h, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.blr x) →
    (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = some h →
    x ≠ .xzr ∧ fileWord file (Arm.r .PC m) = some (Arm.read_mem_bytes 4 (Arm.r .PC m) m) ∧
    I.symAddr h.name 0 = (art I h).base
  plain : ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.reloc? = none →
    ∀ k < 4, ¬ E2E.DeadCleanupBinCheck.RelocAt I (Arm.r .PC m + BitVec.ofNat 64 k)
  /-- the frame's phase 2 at a raising call reads no relocated instruction byte -/
  rest : ∀ d obj t, callDescAt (art I g).fa m = some d → ((uSys I B U).UU M).raise d m = some (obj, t) →
    RestoreOk I (art I g).tables (art I g).base (Arm.r .PC m) t

/-- **The per-state hypothesis on the runs of the machine with unwinding**: at the states of
`ReachU` whose step ends without error, `StepOkU`, and a step that leaves the activation's frame
by unwinding (`UnwExit`) lands on its return (the restored frame is the caller's). -/
def RunOkU (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g c' t, ReachU I B U M f c M' g c' t → Arm.r .ERR ((uSys I B U).machU M' g t) = .None →
    StepOkU I B file U M' g t ∧
    (UnwExit ((uSys I B U).UU M') (art I g).tables (art I g).fa t →
      Returned (art I g) c' ((uSys I B U).machU M' g t))

/-- **The simulation of the activations of the machine with unwinding at depth `M`** by the
executable machine with unwinding: from related entry states, (A) every state of the activation
before its return, not entered by leaving the frame by unwinding, not a pair's second word and
without error, is simulated by a state of the executable's run; (B) when the activation leaves
its frame by unwinding (the state after its step is without error), the executable's run reaches
a raising step whose frame walk is at a frame unwound by its row (`Continues`) to a state
simulating the activation's last state. -/
def ActSimU (M : Nat) : Prop :=
  ∀ g c e, g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → Sim I c e →
    RunOkU I B file U M g c →
    (∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c)) →
      (∀ j, j + 1 = k → ¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa
        (runX ((uSys I B U).machU M g) j c)) →
      ¬ Second I g (Arm.r .PC (runX ((uSys I B U).machU M g) k c)) →
      Arm.r .ERR (runX ((uSys I B U).machU M g) k c) = .None →
      ∃ k', Sim I (runX ((uSys I B U).machU M g) k c) (runX (stepU I B U.Ub file) k' e)) ∧
    (∀ N, (∀ j < N, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c)) →
      ∀ j, j + 1 = N → UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa
        (runX ((uSys I B U).machU M g) j c) →
      Arm.r .ERR (runX ((uSys I B U).machU M g) N c) = .None →
      ∃ k' ra t, Pending I B U.Ub file (runX (stepU I B U.Ub file) k' e) ra
          (xreg 0 (runX ((uSys I B U).machU M g) N c)) t ∧ Continues file ra t ∧
        Sim I (runX ((uSys I B U).machU M g) N c)
          (unwFrame file ra (xreg 0 (runX ((uSys I B U).machU M g) N c)) t))

end Defs

/-! ## Facts of one step -/

section StepFacts

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}

theorem ReachU.mem {M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat}
    {g : Clif.Function} {c' t : Arm.ArmState} (h : ReachU I B U M f c M' g c' t)
    (hf : f ∈ (prog I).funcs) : g ∈ (prog I).funcs := by
  induction h with
  | act _ => exact hf
  | nest _ hc _ _ ih => exact ih (callee_mem hc)

/-- `StepOk` from `StepOkU` and D1 on the linked machine. -/
theorem StepOkU.toStepOk {M : Nat} {g : Clif.Function} {m : Arm.ArmState}
    (h : StepOkU I B file U M g m)
    (hcf : ∀ rl ∈ (art I g).fb.relocs, (rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) →
      Arm.r .PC ((sys I B).mach M g m) = wAt (art I g) (rl.offset + 4) →
      Arm.r .PC m = wAt (art I g) rl.offset) : StepOk I B file M g m :=
  ⟨h.err, h.program, h.site, hcf, h.insn, h.call, h.tls, h.got, h.blr, h.plain⟩

theorem StepOkU.base_eq (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat}
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {m : Arm.ArmState}
    (h : StepOkU I B file U M g m) : progBase m = (art I g).base := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨i, hins, -, -⟩ := h.site
  obtain ⟨j, t, hj, -⟩ := insnAt_spec hins
  exact progBase_of (hF g hg) hm h.program hj

theorem StepOkU.siteAt {M : Nat} {g : Clif.Function} {m : Arm.ArmState}
    (h : StepOkU I B file U M g m) {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) :
    siteAt I (Arm.r .PC m) = some (siteOf (prog I) i) := by
  obtain ⟨i', h1, h2, -⟩ := h.site
  rw [hi] at h1; cases h1; exact h2

/-- `StepOk` at a state at no call (the machines agree there). -/
theorem StepOkU.nocall (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat}
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {m : Arm.ArmState}
    (h : StepOkU I B file U M g m) {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) (h1 : ∀ n, i ≠ .bl n)
    (h2 : ∀ x, i ≠ .blr x) : StepOk I B file M g m := by
  have hb := h.base_eq hF hg
  refine h.toStepOk fun rl hrl ht hpc => h.cf rl hrl ht ?_
  rw [machU_nocall U (by rw [hb]; exact hi) h1 h2]
  exact hpc

/-- `StepOk` at a call of a function of the program (the linked call is at the next word). -/
theorem StepOkU.progCall {M : Nat} {g h : Clif.Function} {m : Arm.ArmState}
    (hok : StepOkU I B file U M g m) (hc : CallsAt I B g m h) : StepOk I B file M g m := by
  refine hok.toStepOk fun rl hrl ht hpc => ?_
  rw [mach_call hc] at hpc
  have hp : Arm.r .PC ((sys I B).pcall M h m) = Arm.r .PC m + 4 := by
    cases M with
    | zero => exact (junkAt_pc m).2
    | succ M => exact (linkedCall_pc _ _ m).2
  rw [hp, ← wAt_add4] at hpc
  exact (BitVec.add_left_inj _).mp hpc

/-- The linked machine at a call of code outside the program: the base hook. -/
theorem mach_base {M : Nat} {g : Clif.Function} {m : Arm.ArmState} {i : Insn}
    {d : Option String} (hi : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some i)
    (hd : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) :
    (sys I B).mach M g m = B.hooks.call d m := by
  show ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m = _
  rcases hd with ⟨n, rfl, hn, rfl⟩ | ⟨x, rfl, hn, rfl⟩
  · simp only [ArmStepX, hi, LinkSys.hooks_call, LinkSys.callHook]
    rw [show (sys I B).P.func? n = none from hn]
    rfl
  · simp only [ArmStepX, hi, LinkSys.hooks_call, LinkSys.callHook]
    rw [show (blrTarget m).bind (symCallee (sys I B).Xb (sys I B).P) = none from hn]
    rfl

/-- `StepOk` at a call of code outside the program whose callee does not raise. -/
theorem StepOkU.baseCall (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat}
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {m : Arm.ArmState}
    (h : StepOkU I B file U M g m) {i : Insn} {d : Option String}
    (hi : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i)
    (hd : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none))
    (hr : U.Ub.raise d m = none) : StepOk I B file M g m := by
  have hb := h.base_eq hF hg
  have hi' : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some i := by rw [hb]; exact hi
  refine h.toStepOk fun rl hrl ht hpc => h.cf rl hrl ht ?_
  rw [machU_base U hi' hd, hr]
  rw [mach_base hi' hd] at hpc
  exact hpc

/-- No raise at a site that is no call of code outside the program. -/
theorem raiseAt_none {s : Arm.ArmState} {i : Insn}
    (hs : siteAt I (Arm.r .PC s) = some (siteOf (prog I) i))
    (h1 : ∀ n, i = .bl n → ((prog I).func? n).isSome)
    (h2 : ∀ x, i = .blr x → ((blrTarget s).bind (symCallee (sys I B).Xb (prog I))).isSome) :
    raiseAt I B U.Ub s = none := by
  unfold raiseAt
  rw [hs]
  cases i with
  | bl n => simp [siteOf, h1 n rfl]
  | blr x => simp [siteOf, h2 x rfl]
  | _ => rfl

/-- The raise at a call of code outside the program is the base callee's. -/
theorem raiseAt_base {s : Arm.ArmState} {i : Insn} {d : Option String}
    (hs : siteAt I (Arm.r .PC s) = some (siteOf (prog I) i))
    (hd : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget s).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) :
    raiseAt I B U.Ub s = U.Ub.raise d s := by
  unfold raiseAt
  rw [hs]
  rcases hd with ⟨n, rfl, hn, rfl⟩ | ⟨x, rfl, hn, rfl⟩
  · simp [siteOf, hn]
  · simp [siteOf, hn]

/-- **The executable's lookup at the return address of a call of `g`** finds `g`'s tables: the
frame's phase 2 on the file is the model's (`Unw.unwindAt` with `g`'s tables at its address). -/
theorem unwFrame_call (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hT : TabsOk I file)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {pc : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base pc = some i) (obj : BitVec 64) (t : Arm.ArmState) :
    unwFrame file (pc + 4) obj t = Unw.unwindAt (art I g).tables (art I g).base pc obj t ∧
    (Continues file (pc + 4) t ↔
      Unw.personality (art I g).tables.lsda (pc + 4 - 1 - (art I g).base).toNat = .continue ∧
      (Unw.restore (Unw.rowAt (art I g).tables.cie (art I g).tables.fde
        (pc + 4 - 1 - (art I g).base).toNat) t).isSome) := by
  have hFg := hF g hg
  obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hi
  have hl := line_lt hFg hj
  have hfit := hFg.fits
  have hlt := (art I g).base.isLt
  have hn : (pc + 4 - 1).toNat = (art I g).base.toNat + lineOffset (art I g).fa.lines.toList j + 3 := by
    rw [← hpc, show (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j) + 4 - 1
      = (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j + 3) by
        rw [BitVec.ofNat_add]; bv_omega]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hlook := hT g hg (pc + 4 - 1).toNat (by omega) (by simp only [FnBin.size]; omega)
  have e4 : pc + 4 - 4 = pc := by bv_omega
  have eb : BitVec.ofNat 64 (art I g).base.toNat = (art I g).base := by simp
  refine ⟨?_, ?_⟩
  · simp only [unwFrame, hlook, eb, e4]
  · simp only [Continues, hlook, Option.some.injEq, Prod.mk.injEq, e4]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h1, h2⟩; rw [eb] at h1 h2; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨_, _, ⟨rfl, rfl⟩, by rw [eb]; exact h1, by rw [eb]; exact h2⟩

/-- The byte before the return address of a call of `g` is code of the program. -/
theorem img_ret (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {pc : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base pc = some i) : img I (pc + 4 - 1) := by
  have hFg := hF g hg
  obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hi
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word hFg.layout hm hj rfl
  refine ⟨(g, art I g), tab_mem (okBCleanup_names hI) hg,
    ((art I g).base + BitVec.ofNat 64 (4 * (0 + lineOffset (art I g).fa.lines.toList j / 4)), w),
    ?_, ?_⟩
  · have := wordsAt_mem (base := (art I g).base) (k := 0) (ws := (art I g).fb.words.toList)
      (j := lineOffset (art I g).fa.lines.toList j / 4) (w := w) (by simpa using hk)
    simpa [FnBin.program] using this
  · rw [← hpc, Nat.zero_add, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)]
    rw [show (art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j) + 4 - 1 -
      ((art I g).base + BitVec.ofNat 64 (lineOffset (art I g).fa.lines.toList j)) = 3 by bv_omega]
    decide

end StepFacts

end E2E.DeadCleanupExecBytes

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The raising steps -/

section Raise

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}

/-- **A raising call of `g` at `pc`**: the model's step is the frame's phase 2 on the restored
state `t`, the executable's raising step's walk is at that frame on a state `t₂` simulating `t`.
If the personality does not continue, the executable's step ends at this frame; if it does, the
frame is unwound (`Continues`), the exception object in x0, the walk's frame simulating the
model's step. -/
theorem frame_out (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hT : TabsOk I file)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {pc : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base pc = some i) {obj : BitVec 64}
    {t t₂ e : Arm.ArmState} (hs : Sim I t t₂)
    (hrest : RestoreOk I (art I g).tables (art I g).base pc t)
    (hpend : Pending I B U.Ub file e (pc + 4) obj t₂)
    (herr : Arm.r .ERR (Unw.unwindAt (art I g).tables (art I g).base pc obj t) = .None) :
    (Unw.personality (art I g).tables.lsda (pc + 4 - 1 - (art I g).base).toNat ≠ .continue →
      Sim I (Unw.unwindAt (art I g).tables (art I g).base pc obj t) (stepU I B U.Ub file e)) ∧
    (Unw.personality (art I g).tables.lsda (pc + 4 - 1 - (art I g).base).toNat = .continue →
      Continues file (pc + 4) t₂ ∧
      xreg 0 (Unw.unwindAt (art I g).tables (art I g).base pc obj t) = obj ∧
      Sim I (Unw.unwindAt (art I g).tables (art I g).base pc obj t)
        (unwFrame file (pc + 4) obj t₂)) := by
  obtain ⟨hU, hC⟩ := unwFrame_call hF hT hg hi obj t₂
  have hsim := unwindAt_sim (obj := obj) hs hrest
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rw [hpend.last (fun hn => hp (hC.1 hn.1).1), hU]
    exact hsim
  · obtain ⟨hr, hx⟩ := unwindAt_continues hp herr
    exact ⟨hC.2 ⟨hp, by rw [restore_isSome_sim hs]; exact hr⟩, hx, by rw [hU]; exact hsim⟩

/-- **A call of code outside the program**: without a raise of its callee the executable's step
simulates the model's; with one, the model's step is the frame's phase 2 and the executable's
raising step's walk is at that frame. -/
theorem base_out (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hT : TabsOk I file)
    (hUS : UnwSim I U.Ub) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m e₀ : Arm.ArmState} (hok : StepOkU I B file U M g m) (hs : Sim I m e₀) {i : Insn}
    {d : Option String} (hi : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i)
    (hd : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none ∧ d = none))
    (herr : Arm.r .ERR ((uSys I B U).machU M g m) = .None) :
    (¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa m →
      Sim I ((uSys I B U).machU M g m) (stepU I B U.Ub file e₀)) ∧
    (UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa m →
      ∃ ra t, Pending I B U.Ub file e₀ ra (xreg 0 ((uSys I B U).machU M g m)) t ∧
        Continues file ra t ∧
        Sim I ((uSys I B U).machU M g m)
          (unwFrame file ra (xreg 0 ((uSys I B U).machU M g m)) t)) := by
  have hFg := hF g hg
  have hb := hok.base_eq hF hg
  have hi' : insnAt (art I g).fa (progBase m) (Arm.r .PC m) = some i := by rw [hb]; exact hi
  have hpe : Arm.r .PC e₀ = Arm.r .PC m := hs.1 .PC
  have hsite : siteAt I (Arm.r .PC e₀) = some (siteOf (prog I) i) := by
    rw [hpe]; exact hok.siteAt hi
  have hd' : (∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
      (∃ x, i = .blr x ∧ (blrTarget e₀).bind (symCallee (sys I B).Xb (prog I)) = none ∧
        d = none) := by
    rcases hd with h | ⟨x, rfl, hn, rfl⟩
    · exact .inl h
    · exact .inr ⟨x, rfl, by rw [blrTarget_sim hs (hok.plain _ hi rfl)]; exact hn, rfl⟩
  have hra : raiseAt I B U.Ub e₀ = U.Ub.raise d e₀ := raiseAt_base hsite hd'
  have hcd : callDescAt (art I g).fa m = some d := by
    unfold callDescAt
    rw [hi']
    rcases hd with ⟨n, rfl, -, rfl⟩ | ⟨x, rfl, -, rfl⟩ <;> rfl
  have hbd : (uSys I B U).BaseDest d := by
    rcases hd with ⟨n, -, hn, rfl⟩ | ⟨x, -, -, rfl⟩
    · exact .inr ⟨n, rfl, hn⟩
    · exact .inl rfl
  have hUU : ((uSys I B U).UU M).raise d m = U.Ub.raise d m :=
    (uSys I B U).UU_base hbd m fun hdn => by
      subst hdn
      rcases hd with ⟨n, -, -, h⟩ | ⟨x, -, h, -⟩
      · cases h
      · exact h
  have hmach := machU_base (B := B) U (M := M) hi' hd
  cases hr : U.Ub.raise d m with
  | none =>
    have hn : ¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa m := by
      rintro ⟨d', obj, t, hd'', hr', -⟩
      rw [hcd] at hd''
      cases hd''
      rw [hUU, hr] at hr'
      cases hr'
    refine ⟨fun _ => ?_, fun hx => absurd hx hn⟩
    rw [stepU_of_none (by rw [hra]; exact hUS.none d m e₀ hs hr), hmach, hr]
    dsimp only
    rw [← mach_base (M := M) hi' hd]
    refine hook_step hFg (hok.baseCall hF hg hi hd hr) hs hi ?_
    rcases hd with ⟨n, rfl, hn, -⟩ | ⟨x, rfl, hn, -⟩
    · exact .inl ⟨n, rfl, hn⟩
    · exact .inr (.inl ⟨x, rfl, hn⟩)
  | some p =>
    obtain ⟨obj, t⟩ := p
    obtain ⟨t₂, hr₂, hst⟩ := hUS.raise d m e₀ obj t hs hr
    have hpend : Pending I B U.Ub file e₀ (Arm.r .PC m + 4) obj t₂ := by
      rw [← hpe]; exact pending_raise (by rw [hra]; exact hr₂)
    have hrest := hok.rest d obj t hcd (by rw [hUU]; exact hr)
    rw [hmach, hr] at herr ⊢
    dsimp only at herr ⊢
    rw [hb] at herr ⊢
    have fo := frame_out hF hT hg hi hst hrest hpend herr
    refine ⟨fun hn => fo.1 fun hp => hn ⟨d, obj, t, hcd, by rw [hUU]; exact hr, by rw [hb]; exact hp⟩,
      fun hx => ?_⟩
    obtain ⟨d', obj', t', hd'', hr', hp⟩ := hx
    rw [hcd] at hd''
    cases hd''
    rw [hUU, hr] at hr'
    cases hr'
    rw [hb] at hp
    obtain ⟨hc, hx0, hsm⟩ := fo.2 hp
    exact ⟨Arm.r .PC m + 4, t₂, by rw [hx0]; exact hpend, hc, by rw [hx0]; exact hsm⟩

/-- The return address of a call of `h` is no second word of a pair of `h` reached in `h`'s
activation (`ret_not_secondN` on the machine with unwinding). -/
theorem ret_not_secondU (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M M' : Nat}
    {g h : Clif.Function} (hg : g ∈ (prog I).funcs) (hh : h ∈ (prog I).funcs) {m : Arm.ArmState}
    (hok0 : StepOkU I B file U M g m) (hc : CallsAt I B g m h)
    (hrun' : RunOkU I B file U M' h (enterAt (art I h) m)) {N : Nat}
    (hN : RetOf (art I h) m (runX ((uSys I B U).machU M' h) N (enterAt (art I h) m)))
    (hmin : ∀ j < N,
      ¬ RetOf (art I h) m (runX ((uSys I B U).machU M' h) j (enterAt (art I h) m))) :
    ¬ Second I h (Arm.r .PC (runX ((uSys I B U).machU M' h) N (enterAt (art I h) m))) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hFh := hF h hh
  cases N with
  | zero => exact not_second_base hFh ⟨rl, hrl, ht, (pc_enterAt (art I h) m).symm.trans he⟩
  | succ N1 =>
  have hokc := (hrun' _ _ _ _
    (ReachU.act (k := N1) fun j hj => fun hr => hmin j (by omega) (returned_iff.2 hr))
    (by rw [← runX_succ' ((uSys I B U).machU M' h)]; exact hN.2.1)).1
  have hpc1 := hokc.cf rl hrl ht (by rw [← runX_succ' ((uSys I B U).machU M' h) N1]; exact he)
  obtain ⟨j, i1, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFh.layout rl).1 hrl
  have hins1 : insnAt (art I h).fa (art I h).base (wAt (art I h) rl.offset) = some i1 := by
    rw [← ho]; exact insnAt_of_line hFh hj
  have hs1 : siteAt I (wAt (art I h) rl.offset) = some (siteOf (prog I) i1) := by
    rw [← hpc1] at hins1 ⊢; exact hokc.siteAt hins1
  have hpcm : Arm.r .PC m = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC m + 4 = wAt (art I h) rl.offset + 4 := by rw [← hN.1, he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  have hb := hok0.base_eq hF hg
  obtain ⟨i0, hi0, hs0, -⟩ := hok0.site
  simp only [CallsAt, hb] at hc
  rw [hpcm, hs1, siteOf_pairFirst hi ht] at hs0
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩ <;> rw [hins] at hi0 <;> cases hi0
  · simp [siteOf, hn] at hs0
  · simp [siteOf] at hs0

/-- **A call of a function `h` of the program**: the executable's word enters `h`; if `h`'s
activation returns, the executable's run reaches the model's return (`ActSimU`'s (A) one level
down); if it leaves its frame by unwinding, the walk of the executable's raising step, one level
down, moves on to the caller's frame, where the model's step is that frame's phase 2. -/
theorem prog_out (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : TabsOk I file) {M : Nat} {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m e₀ : Arm.ArmState} (hok : StepOkU I B file U M g m) (hs : Sim I m e₀)
    (hc : CallsAt I B g m h) (herr : Arm.r .ERR ((uSys I B U).machU M g m) = .None)
    (hcall : ∀ M', M = M' + 1 → ActSimU I B file U M')
    (hrun' : ∀ M', M = M' + 1 → RunOkU I B file U M' h (enterAt (art I h) m)) :
    (¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa m →
      ∃ n, Sim I ((uSys I B U).machU M g m) (runX (stepU I B U.Ub file) n e₀)) ∧
    (UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa m →
      ∃ n ra t, Pending I B U.Ub file (runX (stepU I B U.Ub file) n e₀) ra
          (xreg 0 ((uSys I B U).machU M g m)) t ∧ Continues file ra t ∧
        Sim I ((uSys I B U).machU M g m)
          (unwFrame file ra (xreg 0 ((uSys I B U).machU M g m)) t)) := by
  have hh := callee_mem hc
  have hFg := hF g hg
  have hb := hok.base_eq hF hg
  obtain ⟨i, hi, -, -⟩ := hok.site
  have hpe : Arm.r .PC e₀ = Arm.r .PC m := hs.1 .PC
  have hsite : siteAt I (Arm.r .PC e₀) = some (siteOf (prog I) i) := by
    rw [hpe]; exact hok.siteAt hi
  obtain ⟨d, hcd, hUU, hk⟩ : ∃ d, callDescAt (art I g).fa m = some d ∧
      ((uSys I B U).UU M).raise d m = (uSys I B U).praiseU M h m ∧
      ((∃ n, i = .bl n ∧ (prog I).func? n = some h) ∨
        (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = some h)) := by
    rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
    · rw [hb, hi] at hins
      cases hins
      refine ⟨some n, ?_, (uSys I B U).UU_some hn m, .inl ⟨n, rfl, hn⟩⟩
      unfold callDescAt; rw [hb, hi]
    · rw [hb, hi] at hins
      cases hins
      refine ⟨none, ?_, (uSys I B U).UU_none hcal, .inr ⟨x, rfl, hcal⟩⟩
      unfold callDescAt; rw [hb, hi]
  have hst : stepU I B U.Ub file e₀ = step I B file e₀ := by
    refine stepU_of_none (raiseAt_none hsite (fun n hn => ?_) (fun x hx => ?_))
    · rcases hk with ⟨n', hn', hf⟩ | ⟨x, hx, -⟩
      · rw [hn] at hn'; cases hn'; rw [hf]; rfl
      · rw [hn] at hx; cases hx
    · rcases hk with ⟨n', hn', -⟩ | ⟨x', hx', hf⟩
      · rw [hx] at hn'; cases hn'
      · rw [blrTarget_sim hs (hok.plain _ hi (by rw [hx']; rfl)), hf]; rfl
  have hent := call_enter hFg (hF h hh) (hok.progCall hc) hs hc
  rw [← hst] at hent
  have hmach := machU_prog (B := B) U (M := M) hc
  cases M with
  | zero =>
    rw [hmach] at herr
    exact absurd herr (junkAt_err _)
  | succ M' =>
  by_cases hx : ExitU ((uSys I B U).machU M' h) ((uSys I B U).UU M') (art I h).tables (art I h) m
  · -- the callee's run leaves its frame by unwinding: the call raises
    have hpr : (uSys I B U).praiseU (M' + 1) h m =
        some (xreg 0 (linkedCall ((uSys I B U).machU M' h) (art I h) m),
          linkedCall ((uSys I B U).machU M' h) (art I h) m) := by
      simp only [LinkSysU.praiseU, raisedCall]; exact ite_eq_left hx
    obtain ⟨hex, hpos, hux⟩ := hx
    obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
    obtain ⟨n₂, ra₀, t₀, hpend, hcont, hsim₀⟩ :=
      (hcall M' rfl h _ _ hh (pc_enterAt _ _) hent (hrun' M' rfl)).2 _
        (fun j hj hr => hmin j hj (returned_iff.2 hr)) _ (by omega) hux hN.2.1
    have hv : linkedCall ((uSys I B U).machU M' h) (art I h) m =
        Arm.set_program (runX ((uSys I B U).machU M' h) (firstNat _ hex) (enterAt (art I h) m))
          m.program := by
      simp only [linkedCall, hex, ↓reduceDIte]
    generalize hw : runX ((uSys I B U).machU M' h) (firstNat _ hex) (enterAt (art I h) m) = w
      at hN hpend hsim₀ hv
    have hpcu : Arm.r .PC (unwFrame file ra₀ (xreg 0 w) t₀) = Arm.r .PC m + 4 := by
      rw [hsim₀.1 .PC]; exact hN.1
    have hnext : NextFrame I file ra₀ (xreg 0 w) t₀ :=
      ⟨hcont, by rw [hpcu]; exact img_ret hI hF hg hi⟩
    have hpend' := hpend.next hnext
    rw [hpcu] at hpend'
    have hx0 : xreg 0 (linkedCall ((uSys I B U).machU M' h) (art I h) m) = xreg 0 w := by
      rw [hv]; simp only [xreg, r_set_program]
    have hsv : Sim I (linkedCall ((uSys I B U).machU M' h) (art I h) m)
        (unwFrame file ra₀ (xreg 0 w) t₀) := by
      rw [hv]; exact sim_set_program _ hsim₀
    have hrest := hok.rest d _ _ hcd (by rw [hUU, hpr])
    rw [hmach, hpr] at herr ⊢
    dsimp only at herr ⊢
    rw [hb] at herr ⊢
    rw [hx0] at herr ⊢
    have fo := frame_out hF hT hg hi hsv hrest hpend' herr
    have hidx : runX (stepU I B U.Ub file) (1 + n₂ + 1) e₀ =
        stepU I B U.Ub file (runX (stepU I B U.Ub file) n₂ (stepU I B U.Ub file e₀)) := by
      rw [runX_add, runX_add]; rfl
    refine ⟨fun hn => ⟨1 + n₂ + 1, ?_⟩, fun hu => ?_⟩
    · rw [hidx]
      refine fo.1 fun hp => hn ⟨d, _, _, hcd, by rw [hUU, hpr], ?_⟩
      rw [hb]; exact hp
    · obtain ⟨d', obj', t', hd', hr', hp⟩ := hu
      rw [hcd] at hd'
      cases hd'
      rw [hb] at hp
      obtain ⟨hcn, hx0', hsm⟩ := fo.2 hp
      refine ⟨1 + n₂, _, _, ?_, hcn, by rw [hx0']; exact hsm⟩
      rw [hx0', runX_add]
      exact hpend'
  · -- the callee returns: the linked call
    have hpr : (uSys I B U).praiseU (M' + 1) h m = none := by
      simp only [LinkSysU.praiseU, raisedCall]; exact ite_eq_right hx
    have hnu : ¬ UnwExit ((uSys I B U).UU (M' + 1)) (art I g).tables (art I g).fa m := by
      rintro ⟨d', o, t, hd', hr', -⟩
      rw [hcd] at hd'
      cases hd'
      rw [hUU, hpr] at hr'
      cases hr'
    refine ⟨fun _ => ?_, fun hu => absurd hu hnu⟩
    have hpc : (uSys I B U).pcallU (M' + 1) h m = linkedCall ((uSys I B U).machU M' h) (art I h) m := by
      simp only [LinkSysU.pcallU, returnedCall]; exact ite_eq_right hx
    rw [hmach, hpr] at herr ⊢
    dsimp only at herr ⊢
    rw [hpc] at herr ⊢
    unfold linkedCall at herr ⊢
    split
    · rename_i hex
      obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
      obtain ⟨k2, hk2⟩ := (hcall M' rfl h _ _ hh (pc_enterAt _ _) hent (hrun' M' rfl)).1 _
        (fun j hj hr => hmin j hj (returned_iff.2 hr))
        (fun j hj hu => hx ⟨hex, by omega, by rw [show firstNat _ hex - 1 = j by omega]; exact hu⟩)
        (ret_not_secondU hF hg hh hok hc (hrun' M' rfl) hN hmin) hN.2.1
      exact ⟨1 + k2, by rw [runX_add]; exact sim_set_program _ hk2⟩
    · rename_i hne
      simp only [hne, ↓reduceDIte] at herr
      exact absurd herr (junkAt_err _)


end Raise
end E2E.DeadCleanupExecBytes

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The simulation -/

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}

/-- The instruction at a pair's second word is no call. -/
theorem second_nocall {g : Clif.Function} (hF : FnOk I file g) {pc : BitVec 64} {i : Insn}
    (hs : Second I g pc) (hi : insnAt (art I g).fa (art I g).base pc = some i) :
    (∀ n, i ≠ .bl n) ∧ ∀ x, i ≠ .blr x := by
  obtain ⟨rl, hrl, ht, rfl⟩ := hs
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hF hrl ht
  obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have h2 : insnAt (art I g).fa (art I g).base (wAt (art I g) (rl.offset + 4)) = some i' := by
    rw [← hr'o, ← ho']; exact insnAt_of_line hF hj'
  rw [hi] at h2
  cases h2
  rw [hr't] at hi'
  constructor
  · rintro n rfl
    simp only [Insn.reloc?, Option.some.injEq, Prod.mk.injEq] at hi'
    rcases ht with h | h <;> rw [h] at hi' <;> simp [loOf] at hi'
  · rintro x rfl
    simp [Insn.reloc?] at hi'

/-- Before a state the activation has not returned at, no step left its frame by unwinding
(such a step lands on the return, `RunOkU`). -/
theorem no_exit_before {M : Nat} {g : Clif.Function} {c : Arm.ArmState}
    (hrun : RunOkU I B file U M g c) {k : Nat}
    (hret : ∀ j ≤ k, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c))
    (herr : Arm.r .ERR (runX ((uSys I B U).machU M g) k c) = .None) :
    ∀ j, j + 1 = k → ¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa
      (runX ((uSys I B U).machU M g) j c) := by
  rintro j rfl hu
  refine hret (j + 1) (Nat.le_refl _) ?_
  rw [runX_succ']
  exact (hrun _ _ _ _ (ReachU.act fun j' hj' => hret j' (by omega))
    (by rw [← runX_succ' ((uSys I B U).machU M g)]; exact herr)).2 hu

theorem act_coreU (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : TabsOk I file) (hUS : UnwSim I U.Ub) (M : Nat)
    (hcall : ∀ M', M = M' + 1 → ActSimU I B file U M') : ActSimU I B file U M := by
  intro g c e hg hpc hsim hrun
  have hFg := hF g hg
  have hok : ∀ j, (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j' c)) →
      Arm.r .ERR (runX ((uSys I B U).machU M g) (j + 1) c) = .None →
      StepOkU I B file U M g (runX ((uSys I B U).machU M g) j c) := fun j hj he =>
    (hrun _ _ _ _ (ReachU.act hj) (by rw [← runX_succ' ((uSys I B U).machU M g)]; exact he)).1
  have hrun' : ∀ k0 h, (∀ j ≤ k0, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c)) →
      CallsAt I B g (runX ((uSys I B U).machU M g) k0 c) h →
      Arm.r .ERR (runX ((uSys I B U).machU M g) (k0 + 1) c) = .None →
      ∀ M', M = M' + 1 →
        RunOkU I B file U M' h (enterAt (art I h) (runX ((uSys I B U).machU M g) k0 c)) := by
    intro k0 h hj hc he M' hM
    subst hM
    exact fun M'' g' c' t hr he' => hrun _ _ _ _ (ReachU.nest hj hc he hr) he'
  have hA : ∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((uSys I B U).machU M g) j c)) →
      (∀ j, j + 1 = k → ¬ UnwExit ((uSys I B U).UU M) (art I g).tables (art I g).fa
        (runX ((uSys I B U).machU M g) j c)) →
      ¬ Second I g (Arm.r .PC (runX ((uSys I B U).machU M g) k c)) →
      Arm.r .ERR (runX ((uSys I B U).machU M g) k c) = .None →
      ∃ k', Sim I (runX ((uSys I B U).machU M g) k c) (runX (stepU I B U.Ub file) k' e) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
    intro hret hnu hsec herr
    cases k with
    | zero => exact ⟨0, hsim⟩
    | succ k0 =>
    have hok0 := hok k0 (fun j hj => hret j (by omega)) herr
    have hnu0 := hnu k0 rfl
    rw [runX_succ'] at hsec herr ⊢
    by_cases hs : Second I g (Arm.r .PC (runX ((uSys I B U).machU M g) k0 c))
    · -- the second word of a pair: two steps from its first word
      have hs' := hs
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases k0 with
      | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
      | succ k1 =>
      have hok1 := hok k1 (fun j hj => hret j (by omega)) hok0.err
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((uSys I B U).machU M g) k1]; exact he)
      obtain ⟨j1, i1, t1, hj1, hi1, ho1⟩ := (FnAsm.layout_relocs hFg.layout rl).1 hrl
      have hins1 : insnAt (art I g).fa (art I g).base
          (Arm.r .PC (runX ((uSys I B U).machU M g) k1 c)) = some i1 := by
        rw [hpc1, ← ho1]; exact insnAt_of_line hFg hj1
      have hnc1 : (∀ n, i1 ≠ .bl n) ∧ ∀ x, i1 ≠ .blr x := by
        constructor
        · rintro n rfl; simp only [Insn.reloc?, Option.some.injEq, Prod.mk.injEq] at hi1
          rcases ht with h | h <;> rw [h] at hi1 <;> simp at hi1
        · rintro x rfl; simp [Insn.reloc?] at hi1
      have hsec1 : ¬ Second I g (Arm.r .PC (runX ((uSys I B U).machU M g) k1 c)) := by
        rw [hpc1]; exact first_not_second hFg hrl ht
      obtain ⟨k', hk'⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
        (no_exit_before hrun (fun j hj => hret j (by omega)) hok1.err) hsec1 hok1.err
      obtain ⟨i0, hins0, -, -⟩ := hok0.site
      have hnc0 := second_nocall hFg hs' hins0
      have hb1 := hok1.base_eq hF hg
      have hb0 := hok0.base_eq hF hg
      have hst1 := hok1.nocall hF hg hins1 hnc1.1 hnc1.2
      have hm1 : (uSys I B U).machU M g (runX ((uSys I B U).machU M g) k1 c) =
          (sys I B).mach M g (runX ((uSys I B U).machU M g) k1 c) :=
        machU_nocall U (by rw [hb1]; exact hins1) hnc1.1 hnc1.2
      have hst0 := hok0.nocall hF hg hins0 hnc0.1 hnc0.2
      rw [runX_succ', hm1] at hst0 hins0 hb0
      have hm0 := machU_nocall (B := B) U (M := M) (by rw [hb0]; exact hins0) hnc0.1 hnc0.2
      obtain ⟨hpcE, -⟩ := pair_first_pc hFg hrl ht hpc1 hst1 hk'
      have hs1 : stepU I B U.Ub file (runX (stepU I B U.Ub file) k' e) =
          step I B file (runX (stepU I B U.Ub file) k' e) :=
        stepU_of_none (raiseAt_none (by rw [hk'.1 .PC]; exact siteAt_of hst1 hins1)
          (fun n hn => absurd hn (hnc1.1 n)) (fun x hx => absurd hx (hnc1.2 x)))
      have hs2 : stepU I B U.Ub file (step I B file (runX (stepU I B U.Ub file) k' e)) =
          step I B file (step I B file (runX (stepU I B U.Ub file) k' e)) :=
        stepU_of_none (raiseAt_none (by rw [← hpcE]; exact siteAt_of hst0 hins0)
          (fun n hn => absurd hn (hnc0.1 n)) (fun x hx => absurd hx (hnc0.2 x)))
      refine ⟨k' + 2, ?_⟩
      rw [runX_succ', hm1, hm0, runX_add (stepU I B U.Ub file) k' 2]
      show Sim I _ (stepU I B U.Ub file (stepU I B U.Ub file (runX (stepU I B U.Ub file) k' e)))
      rw [hs1, hs2]
      exact pair_step hFg hrl ht hpc1 hst1 hst0 hk'
    · obtain ⟨k', hk'⟩ := ih k0 (by omega) (fun j hj => hret j (by omega))
        (no_exit_before hrun (fun j hj => hret j (by omega)) hok0.err) hs hok0.err
      obtain ⟨i, hins, -, -⟩ := hok0.site
      have hb := hok0.base_eq hF hg
      have hins' : insnAt (art I g).fa (progBase (runX ((uSys I B U).machU M g) k0 c))
          (Arm.r .PC (runX ((uSys I B U).machU M g) k0 c)) = some i := by rw [hb]; exact hins
      have hsite : siteAt I (Arm.r .PC (runX (stepU I B U.Ub file) k' e)) =
          some (siteOf (prog I) i) := by rw [hk'.1 .PC]; exact hok0.siteAt hins
      have hbase : ∀ d, ((∃ n, i = .bl n ∧ (prog I).func? n = none ∧ d = some n) ∨
          (∃ x, i = .blr x ∧ (blrTarget (runX ((uSys I B U).machU M g) k0 c)).bind
            (symCallee (sys I B).Xb (prog I)) = none ∧ d = none)) →
          ∃ k'', Sim I ((uSys I B U).machU M g (runX ((uSys I B U).machU M g) k0 c))
            (runX (stepU I B U.Ub file) k'' e) := fun d hd =>
        ⟨k' + 1, by rw [runX_succ']; exact (base_out hF hT hUS hg hok0 hk' hins hd herr).1 hnu0⟩
      have hprog : ∀ h, CallsAt I B g (runX ((uSys I B U).machU M g) k0 c) h →
          ∃ k'', Sim I ((uSys I B U).machU M g (runX ((uSys I B U).machU M g) k0 c))
            (runX (stepU I B U.Ub file) k'' e) := fun h hc => by
        obtain ⟨n, hn⟩ := (prog_out hI hF hT hg hok0 hk' hc herr hcall
          (hrun' k0 h (fun j hj => hret j (by omega)) hc (by rw [runX_succ']; exact herr))).1 hnu0
        exact ⟨k' + n, by rw [runX_add]; exact hn⟩
      have hnocall : (∀ n, i ≠ .bl n) → (∀ x, i ≠ .blr x) →
          (uSys I B U).machU M g (runX ((uSys I B U).machU M g) k0 c) =
            (sys I B).mach M g (runX ((uSys I B U).machU M g) k0 c) ∧
          stepU I B U.Ub file (runX (stepU I B U.Ub file) k' e) =
            step I B file (runX (stepU I B U.Ub file) k' e) ∧
          StepOk I B file M g (runX ((uSys I B U).machU M g) k0 c) := fun h1 h2 =>
        ⟨machU_nocall U hins' h1 h2, stepU_of_none (raiseAt_none hsite
          (fun n hn => absurd hn (h1 n)) (fun x hx => absurd hx (h2 x))),
          hok0.nocall hF hg hins h1 h2⟩
      by_cases hhk : i.hooked = false
      · obtain ⟨e1, e2, hst⟩ := hnocall (fun n h => by subst h; cases hhk)
          (fun x h => by subst h; cases hhk)
        exact ⟨k' + 1, by rw [runX_succ', e1, e2]; exact plain_step hFg hst hk' hins hhk⟩
      · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true,
          not_true_eq_false] at hhk
        case bl n =>
          cases hn : (prog I).func? n with
          | none => exact hbase (some n) (.inl ⟨n, rfl, hn, rfl⟩)
          | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
        case blr x =>
          cases hn : (blrTarget (runX ((uSys I B U).machU M g) k0 c)).bind
              (symCallee (sys I B).Xb (prog I)) with
          | none => exact hbase none (.inr ⟨x, rfl, hn, rfl⟩)
          | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
        case adrpGot a b =>
          obtain ⟨e1, -, hst⟩ := hnocall (by simp) (by simp)
          exact absurd (by rw [e1]; exact adrp_lands hFg hst hins (.inl ⟨a, b, rfl⟩)) hsec
        case adrp a b d =>
          obtain ⟨e1, -, hst⟩ := hnocall (by simp) (by simp)
          exact absurd (by rw [e1]; exact adrp_lands hFg hst hins (.inr ⟨a, b, d, rfl⟩)) hsec
        case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
        case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
        case adrpTlsDesc a b =>
          obtain ⟨e1, e2, hst⟩ := hnocall (by simp) (by simp)
          exact ⟨k' + 1, by
            rw [runX_succ', e1, e2]
            exact hook_step hFg hst hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩)))⟩
        case ldrTlsDescLo12 a b d =>
          obtain ⟨e1, e2, hst⟩ := hnocall (by simp) (by simp)
          exact ⟨k' + 1, by
            rw [runX_succ', e1, e2]
            exact hook_step hFg hst hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩)))⟩
  refine ⟨hA, ?_⟩
  intro N hret j hj hux herr
  subst hj
  have hokj := hok j (fun j' hj' => hret j' (by omega)) herr
  have hb := hokj.base_eq hF hg
  obtain ⟨i, hins, -, -⟩ := hokj.site
  have hux' := hux
  obtain ⟨d, o, t, hcd, -, -⟩ := hux'
  have hci : (∃ n, i = .bl n) ∨ ∃ x, i = .blr x := by
    unfold callDescAt at hcd
    rw [hb, hins] at hcd
    cases i <;> simp at hcd ⊢
  have hcpc : CallPc (art I g).fa (art I g).base (Arm.r .PC (runX ((uSys I B U).machU M g) j c)) := by
    obtain ⟨j0, t0, hj0, hpc0⟩ := insnAt_spec hins
    exact ⟨j0, i, t0, hj0, hci, hpc0.symm⟩
  obtain ⟨k', hk'⟩ := hA j (fun j' hj' => hret j' (by omega))
    (no_exit_before hrun (fun j' hj' => hret j' (by omega)) hokj.err)
    (not_second_callPc hFg hcpc) hokj.err
  have hrun'' := hrun' j
  rw [runX_succ'] at herr ⊢
  have hprog : ∀ h, CallsAt I B g (runX ((uSys I B U).machU M g) j c) h →
      ∃ k' ra t, Pending I B U.Ub file (runX (stepU I B U.Ub file) k' e) ra
          (xreg 0 ((uSys I B U).machU M g (runX ((uSys I B U).machU M g) j c))) t ∧
        Continues file ra t ∧
        Sim I ((uSys I B U).machU M g (runX ((uSys I B U).machU M g) j c))
          (unwFrame file ra (xreg 0 ((uSys I B U).machU M g (runX ((uSys I B U).machU M g) j c)))
            t) := fun h hc => by
    obtain ⟨n2, ra, t, h1, h2, h3⟩ := (prog_out hI hF hT hg hokj hk' hc herr hcall
      (hrun'' h (fun j' hj' => hret j' (by omega)) hc (by rw [runX_succ']; exact herr))).2 hux
    exact ⟨k' + n2, ra, t, by rw [runX_add]; exact h1, h2, h3⟩
  rcases hci with ⟨n, rfl⟩ | ⟨x, rfl⟩
  · cases hn : (prog I).func? n with
    | none =>
      obtain ⟨ra, t, h1, h2, h3⟩ :=
        (base_out hF hT hUS hg hokj hk' hins (.inl ⟨n, rfl, hn, rfl⟩) herr).2 hux
      exact ⟨k', ra, t, h1, h2, h3⟩
    | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
  · cases hn : (blrTarget (runX ((uSys I B U).machU M g) j c)).bind
        (symCallee (sys I B).Xb (prog I)) with
    | none =>
      obtain ⟨ra, t, h1, h2, h3⟩ :=
        (base_out hF hT hUS hg hokj hk' hins (.inr ⟨x, rfl, hn, rfl⟩) herr).2 hux
      exact ⟨k', ra, t, h1, h2, h3⟩
    | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)

end Core

/-- **The simulation of the machine with unwinding at every depth.** -/
theorem act_simU {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}
    (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hT : TabsOk I file)
    (hUS : UnwSim I U.Ub) : ∀ M, ActSimU I B file U M
  | 0 => act_coreU hI hF hT hUS 0 fun _ h => by cases h
  | M + 1 => act_coreU hI hF hT hUS (M + 1) fun M' h => by
    obtain rfl : M = M' := Nat.succ.inj h
    exact act_simU hI hF hT hUS M

end E2E.DeadCleanupExecBytes

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The theorem about the executable with unwinding -/

/-- **What the executable machine's run does for an outcome of the CLIF run with unwinding**
(`ArmRefinesU`, with the live CLIF bytes compared outside the relocated instruction bytes `R`,
as `ExecRefines`): a return with the results, a trap at a trap site of the function, or the
exception leaving it — an AAPCS64 return to the caller with the exception object in x0 — the
live CLIF bytes outside `R` as the CLIF memory. -/
def ExecRefinesU (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (R : BitVec 64 → Prop) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .unwound e cm => ∃ n, ArmRet ra s (runX astep n s) ∧ ExnRel e (xreg 0 (runX astep n s)) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .stuck _ | .outOfFuel => True

/-- `ExecRefinesU` of a run without exceptions is `ExecRefines` (the normal-return theorem's
conclusion is the restriction). -/
theorem ExecRefinesU.toExec {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o : Clif.Outcome} (h : ExecRefinesU fb base ra astep s R o.toX) :
    ExecRefines fb base ra astep s R o := by
  cases o <;> exact h

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray} {U : LinkSysU}

/-- Before the state where the model's run with unwinding is, the activation has not returned
(`no_return` on the machine with unwinding). -/
theorem no_returnU {M : Nat} {f : Clif.Function} (hFf : FnOk I file f) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    {n : Nat} (herr : Arm.r .ERR (runX ((uSys I B U).machU M f) n c) = .None) :
    ∀ j < n, ¬ Returned (art I f) c (runX ((uSys I B U).machU M f) j c) := by
  intro j hj hr
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFf.layout
  have := retStuckU (X := (sys I B).Xb) (H := (uSys I B U).hooksU M) (U := (uSys I B U).UU M)
    (T := (art I f).tables) hFf.layout hm hr.2.2.1 (by rw [hr.1]; exact hra) (n - j - 1)
  change Arm.r .ERR (runX ((uSys I B U).machU M f) (n - j - 1 + 1)
    (runX ((uSys I B U).machU M f) j c)) ≠ .None at this
  rw [← runX_add, show j + (n - j - 1 + 1) = n by omega] at this
  exact this herr

/-- A trap site of `f` is a code word of `f`. -/
theorem trap_code {f : Clif.Function} (hFf : FnOk I file f) {c : Clif.TrapCode}
    {s : Arm.ArmState} (h : TrapAt (art I f).fb (art I f).base c s) :
    ∃ k < (art I f).fb.words.size, Arm.r .PC s = (art I f).base + BitVec.ofNat 64 (4 * k) := by
  obtain ⟨t, ht, -, hpc⟩ := h.site
  obtain ⟨j, i, hj, ho⟩ := ((FnAsm.layout_traps hFf.layout).2 t).1 ht
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFf.layout
  obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word hFf.layout hm hj rfl
  refine ⟨lineOffset (art I f).fa.lines.toList j / 4, (Array.getElem?_eq_some_iff.mp hk).1, ?_⟩
  rw [hpc, ← ho, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)]

/-- The return of the model's activation transfers to the executable machine's state. -/
theorem armRet_sim {f : Clif.Function} {r t t' : Arm.ArmState} {ra : BitVec 64}
    (h : ArmRet ra (modelOf I f r) t) (hs : Sim I t t') : ArmRet ra r t' :=
  ⟨by rw [hs.1]; exact h.pc, by rw [hs.1]; exact h.err,
    by simp only [spv]; rw [hs.1]; exact h.sp.trans (spv_modelOf I f r),
    fun n hn => by simp only [xreg]; rw [hs.1]; exact (h.savedX n hn).trans (r_modelOf I f r _),
    fun n h8 h16 => by rw [hs.1, h.savedV n h8 h16, r_modelOf]⟩

/-- **The model's outcome with unwinding transfers to the executable machine with unwinding**,
given the per-state facts of the model's run (`RunOkU`), for an outside caller whose call
instruction (the byte before the return address) is no code of the program. -/
theorem exec_of_modelU (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hT : TabsOk I file) (hUS : UnwSim I U.Ub) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hra1 : ¬ img I (xreg 30 r - 1))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → E2E.DeadCleanupBinCheck.RelocAt I a)
    (hrun : RunOkU I B file U M f (modelOf I f r)) {o : Clif.XOutcome}
    (h : ArmRefinesU (art I f).fb (art I f).base (xreg 30 r) ((uSys I B U).machU M f)
      (modelOf I f r) o) :
    ExecRefinesU (art I f).fb (art I f).base (xreg 30 r) (stepU I B U.Ub file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hS := act_simU (B := B) hI hF hT hUS M f _ r hf hpc' hsim hrun
  -- a state of the run at the return address is simulated
  have hfin : ∀ n, (∀ j < n, ¬ Returned (art I f) (modelOf I f r)
        (runX ((uSys I B U).machU M f) j (modelOf I f r))) →
      Arm.r .PC (runX ((uSys I B U).machU M f) n (modelOf I f r)) = xreg 30 r →
      Arm.r .ERR (runX ((uSys I B U).machU M f) n (modelOf I f r)) = .None →
      ∃ k', Sim I (runX ((uSys I B U).machU M f) n (modelOf I f r))
        (runX (stepU I B U.Ub file) k' r) := by
    intro n hret hpcn herr
    have hsec : ¬ Second I f (Arm.r .PC (runX ((uSys I B U).machU M f) n (modelOf I f r))) :=
      fun hs => by
        obtain ⟨k, hk, he⟩ := second_code hFf hs
        exact hra k hk (by rw [← he, hpcn])
    by_cases hu : ∃ j, j + 1 = n ∧ UnwExit ((uSys I B U).UU M) (art I f).tables (art I f).fa
        (runX ((uSys I B U).machU M f) j (modelOf I f r))
    · obtain ⟨j, hj, hux⟩ := hu
      obtain ⟨k', ra, t, hp, -, hsm⟩ := hS.2 n hret j hj hux herr
      have hnn : ¬ NextFrame I file ra
          (xreg 0 (runX ((uSys I B U).machU M f) n (modelOf I f r))) t := fun hn =>
        hra1 (by rw [← hpcn, ← hsm.1 .PC]; exact hn.2)
      exact ⟨k' + 1, by rw [runX_succ', hp.last hnn]; exact hsm⟩
    · exact hS.1 n hret (fun j hj hux => hu ⟨j, hj, hux⟩) hsec herr
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hfin n (no_returnU hFf hra' hret.err) hret.pc hret.err
    refine ⟨k', armRet_sim hret hk', fun j v hv => ?_, fun a b hv hb hR => ?_⟩
    · simp only [xreg]; rw [hk'.1]; exact hx j v hv
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (stepU I B U.Ub file) k' r).mem =
        (runX (stepU I B U.Ub file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | unwound ex cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hfin n (no_returnU hFf hra' hret.err) hret.pc hret.err
    refine ⟨k', armRet_sim hret hk', ?_, fun a b hv hb hR => ?_⟩
    · simp only [xreg]; rw [hk'.1]; exact hx
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (stepU I B U.Ub file) k' r).mem =
        (runX (stepU I B U.Ub file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_returnU (U := U) (B := B) hFf hra' htrap.err
    have hnr : ∀ j ≤ n, ¬ Returned (art I f) (modelOf I f r)
        (runX ((uSys I B U).machU M f) j (modelOf I f r)) := fun j hj hr => by
      rcases Nat.lt_or_ge j n with h | h
      · exact hguard j h hr
      · obtain rfl : j = n := by omega
        obtain ⟨k, hk, he⟩ := trap_code hFf htrap
        exact hra' k hk (by rw [← hr.1, he])
    have hnu := no_exit_before hrun hnr htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((uSys I B U).machU M f) n (modelOf I f r)))
    · -- a trap at a second word: one executable step after the first word
      have hs' := hs
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := (hrun _ _ _ _ (ReachU.act (k := n1) fun j hj => hnr j (by omega))
        (by rw [← runX_succ' ((uSys I B U).machU M f)]; exact htrap.err)).1
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((uSys I B U).machU M f) n1]; exact he)
      obtain ⟨j1, i1, t1, hj1, hi1, ho1⟩ := (FnAsm.layout_relocs hFf.layout rl).1 hrl
      have hins1 : insnAt (art I f).fa (art I f).base
          (Arm.r .PC (runX ((uSys I B U).machU M f) n1 (modelOf I f r))) = some i1 := by
        rw [hpc1, ← ho1]; exact insnAt_of_line hFf hj1
      have hnc1 : (∀ n, i1 ≠ .bl n) ∧ ∀ x, i1 ≠ .blr x := by
        constructor
        · rintro n rfl; simp only [Insn.reloc?, Option.some.injEq, Prod.mk.injEq] at hi1
          rcases ht with h | h <;> rw [h] at hi1 <;> simp at hi1
        · rintro x rfl; simp [Insn.reloc?] at hi1
      obtain ⟨k', hk'⟩ := hS.1 n1 (fun j hj => hguard j (by omega))
        (no_exit_before hrun (fun j hj => hnr j (by omega)) hok1.err)
        (by rw [hpc1]; exact first_not_second hFf hrl ht) hok1.err
      have hst1 := hok1.nocall hF hf hins1 hnc1.1 hnc1.2
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hst1 hk'
      have hm1 : (uSys I B U).machU M f (runX ((uSys I B U).machU M f) n1 (modelOf I f r)) =
          (sys I B).mach M f (runX ((uSys I B U).machU M f) n1 (modelOf I f r)) :=
        machU_nocall U (by rw [hok1.base_eq hF hf]; exact hins1) hnc1.1 hnc1.2
      have hs1 : stepU I B U.Ub file (runX (stepU I B U.Ub file) k' r) =
          step I B file (runX (stepU I B U.Ub file) k' r) :=
        stepU_of_none (raiseAt_none (by rw [hk'.1 .PC]; exact siteAt_of hst1 hins1)
          (fun n hn => absurd hn (hnc1.1 n)) (fun x hx => absurd hx (hnc1.2 x)))
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ', hm1] at htrap
      rw [runX_succ', hs1]
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hS.1 n hguard hnu hs htrap.err
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial

end Transfer

end E2E.DeadCleanupExecBytes
