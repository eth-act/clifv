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
