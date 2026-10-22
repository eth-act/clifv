import FV.E2E.DeadCleanupExecRunN
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
