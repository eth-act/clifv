module

public import FV.Concurrency.CallThread
public import FV.Concurrency.ArmAllocEntry
public import FV.Concurrency.ArmAllocFwd
public import FV.Concurrency.ArmProgram

@[expose] public section

/-!
# Private segments, the `bl` step and exclusive-closed runs (T2h, #311, calls)

The pieces the caller's segment obligation (`CallCompose.SegOk`) needs, and the exclusive-closed
runs of callees with LL/SC loops:

* `moves_privA`: through a list of moves at the head of the items, the single-core run, `Q ∧
  AInv` after it, and **per step** its events private and no store exclusive (`move_lines`);
* `prun_privF`: a precise run under `OkPriv` of a machine `f` agreeing with `R.step` along the
  single-core path through such steps is that path; its labels are the path's events, none a
  failed store exclusive or a `relXW` (`prun_priv` for a linked machine);
* `step_bl`: **the machine's step at a hooked `bl n` line** is the call hook `R.H.call (some n)`;
  the decoded instruction (`BL`) has no events and class `plain`; `tstep_plain_nil`: every
  precise thread step there has the empty label and the machine's state;
* `refines_nilS`: event-free CLIF steps refine an Arm segment of private writes;
* **`xClosed_mon`**: on a program whose load exclusives all acquire, with a base other than `sp`
  (`LdxAcq`), and a machine keeping the program and the error, every precise run from the open
  monitor is exclusive-closed (a successful store exclusive needs the armed monitor, which only
  an `ldaxr` with its `acqXR` event arms); with `armStepX_err`, `funReal_callee0`/
  **`funReal_calleeX`**: the callee contract of a compiled callee (e.g. with `atomic_rmw` /
  `atomic_cas` loops) entered with the open monitor, from that check of its program.
-/

namespace Concurrency.CallSeg

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot CallThread

/-! ## Private segments -/

/-- **The machine keeps the program through straight-line lines.** -/
theorem linesAt_program {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') :
    ∀ i ≤ ls1.length, (iterN R.step i s).program = R.fb.program R.base
  | 0, _ => h.prog
  | i + 1, hi => by
    obtain ⟨x, t, a, -, -, -, -, hit⟩ := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit
      h.at_ h.hook h.prog h.pc h.err h.inter h.run i (by omega)
    rw [show R.step = ArmStepX R.X R.H R.fa from rfl, hit, exec_inst_program]
    exact linesAt_program hR h i (by omega)

/-- **Through a list of moves**, per step (module doc). -/
theorem moves_privA {R : RL} (hR : R.Wf) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV),
      Q R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      AInv R (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, movesM mvs m, w⟩) ∧
        AInv R (.run ⟨b, its, movesM mvs m, w⟩) ∧
        ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
          (iterN R.step i s).program = R.fb.program R.base
  | [], its, s, m, hq, hA => ⟨0, hq, hA, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | p :: mvs, its, s, m, hq, hA => by
    obtain ⟨j, ls1, s', code, -, -, hlat, hq1, hpriv⟩ := move_lines hR hq
    have hA1 := Backend.Proof.aInv_step hR hq hA (.move (src := p.1) (dst := p.2))
    have hit := hlat.iter hR
    rw [← hit] at hq1
    obtain ⟨n, hq2, hA2, hp2⟩ := moves_privA hR mvs its _ _ hq1 hA1
    refine ⟨ls1.length + n, by rw [iterN_add]; exact hq2, hA2, fun i hi => ?_⟩
    by_cases h : i < ls1.length
    · exact ⟨hpriv i h, linesAt_program hR hlat i (by omega)⟩
    · have := hp2 (i - ls1.length) (by omega)
      rw [← iterN_add, show ls1.length + (i - ls1.length) = i by omega] at this
      exact this

/-- **A precise run of a machine agreeing with `R.step` along a private single-core path** is
that path (module doc). -/
theorem prun_privF {R : RL} {f : ArmState → ArmState} :
    ∀ {L : List Lab} {s : ArmState} {mon : Mon} {t' : ArmState × Mon},
    PRun Policy.arm f (OkPriv R) (s, mon) L t' →
    (∀ i < L.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧
      NoStx (iterN R.step i s) ∧ f (iterN R.step i s) = R.step (iterN R.step i s)) →
    t'.1 = iterN R.step L.length s ∧ evTr L = segEvs R.step L.length s ∧
      ∀ l ∈ L, l.xfail = false ∧ ∀ e ∈ l.evs, e.k ≠ .relXW
  | [], _, _, _, .nil, _ => ⟨rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩
  | l :: L, s, mon, t', .cons (t1 := t1) hs hp ho hr, h => by
    obtain ⟨hpv, hx, hf⟩ := h 0 (by simp)
    simp only [iterN] at hpv hx hf
    have hxf : l.xfail = false := by
      cases hs with
      | exec => rfl
      | xfail hc => exact absurd hc (hx _ _ _)
    have hag : Agrees l.evs s.mem := by
      intro e he hRd
      rcases hp with h' | ⟨M, hM⟩
      · rw [hxf] at h'; cases h'
      · have he' := he
        rw [hM, ArmPrecise.stepEvs_setMem] at he'
        obtain ⟨e0, he0, -, ha, -⟩ := mem_reread he'
        exact ho e he hRd (privA_addr.2 (ha ▸ hpv e0 he0))
    have hk : ∀ e ∈ l.evs, e.k ≠ .relXW := by
      cases hs with
      | exec hk' =>
        intro e he hke
        have := hk'.1 e he
        rw [hke] at this
        cases hc : cls s <;> rw [hc] at this <;> simp [Cls.kind, AKind.dir] at this
        exact hx _ _ _ hc
      | xfail => intro e he; exact absurd he List.not_mem_nil
    obtain ⟨h1, h2, -⟩ := tstep_own hs hp hag hxf
    obtain ⟨s1, mon1⟩ := t1
    simp only at h1
    rw [hf] at h1
    subst h1
    have ih := prun_privF hr fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [iterN] using this
    refine ⟨by simpa [iterN] using ih.1, ?_, ?_⟩
    · simp only [evTr, List.map_cons, List.length_cons, segEvs] at ih ⊢
      rw [h2, ← ih.2.1]
    · intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact ⟨hxf, hk⟩
      · exact ih.2.2 l' hl'

/-! ## The `bl` step -/

/-- **The machine's step at a hooked `bl n` line** (module doc). -/
theorem step_bl {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {n : String}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins (.bl n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = R.H.call (some n) s ∧ stepEvs s = [] ∧ cls s = .plain := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hne : R.fb.words.toList ≠ [] := by
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase s = R.base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hR.layout
  have hfit := hR.fit
  have hins : insnAt R.fa (progBase s) (Arm.r .PC s) = some (.bl n) := by
    rw [hb, hpc]; exact insnAt_line (by omega) hj
  have hstep : R.step s = R.H.call (some n) s := by
    show ArmStepX R.X R.H R.fa s = _
    unfold ArmStepX
    simp only [hins]
  have ha : (Insn.bl n).toArmInst ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ =
      .ok (.BR (.Uncond_branch_imm { op := 1, imm26 := 0 })) := rfl
  have hfetch : fetch_inst (Arm.r .PC s) s = some w := by
    rw [fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := R.base) (by have := (FnAsm.layout_size hR.layout).1; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  have hd := Insn.decode_encode_of ha hw
  have hdec : decodeAt s = some (.BR (.Uncond_branch_imm { op := 1, imm26 := 0 })) := by
    simp only [decodeAt, hfetch, hd]
  refine ⟨hstep, ?_, ?_⟩
  · simp only [stepEvs, hdec]
    split <;> rfl
  · unfold cls
    rw [hdec]

/-- **A precise thread step at an instruction without events of class `plain`**: the empty label,
the machine's state, the monitor kept. -/
theorem tstep_plain_nil {P : Policy} {f : ArmState → ArmState} {s : ArmState} {mon : Mon}
    {l : Lab} {t1 : ArmState × Mon} (hs : TStep P f (s, mon) l t1) (hp : ArmPrecise.Precise s l)
    (he : stepEvs s = []) (hc : cls s = .plain) : l = ⟨[], false⟩ ∧ t1 = (f s, mon) := by
  cases hs with
  | exec =>
    rcases hp with h | ⟨m, hm⟩
    · cases h
    · rw [ArmPrecise.stepEvs_setMem, he] at hm
      simp only [ArmPrecise.reread, List.map_nil] at hm
      subst hm
      refine ⟨rfl, ?_⟩
      simp only [applyR, setMem_self, hc, monAfter]
  | xfail hc' => rw [hc] at hc'; cases hc'

/-! ## Event-free CLIF steps -/

theorem evAt_nilS {α : Type} {tr : List (List α)} (h : ∀ x ∈ tr, x = []) (p : Nat × Nat) :
    evAt tr p = none := by
  unfold evAt
  cases hp : tr[p.1]? with
  | none => rfl
  | some x =>
    have := h x (List.mem_of_getElem? hp)
    subst this
    simp

/-- **Event-free CLIF steps refine an Arm segment of private writes.** -/
theorem refines_nilS {K : Type} {MK : K → AKind → Prop} {Priv : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K BVal))} {T : List (List Ev)}
    (hS : ∀ x ∈ trS, x = []) (hW : PrivW Priv T) : Refines MK Priv pairT trS (conv T) id where
  ev p x hx := by rw [evAt_nilS hS] at hx; cases hx
  mono p _ hp := by rw [evAt_nilS hS] at hp; cases hp
  shared p x hx := by rw [evAt_nilS hS] at hx; cases hx
  priv p y hy hd _ := by
    rw [evAt_conv] at hy
    cases hx : evAt T p with
    | none => rw [hx] at hy; cases hy
    | some x =>
      rw [hx] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      exact (hW p x hx hd).1
  len j hj := by rw [hS _ (List.getElem_mem hj)]; simp
  pair j hj h2 := by rw [hS _ (List.getElem_mem hj)] at h2; cases h2
  pair_inv p _ hp := by rw [evAt_nilS hS] at hp; cases hp

/-! ## Exclusive-closed runs from the open monitor -/

/-- **Every load exclusive at `s` acquires and has a base other than `sp`.** -/
def LdxAcq (s : ArmState) : Prop := ∀ a rn sz, cls s = .ldx a rn sz → a = true ∧ rn ≠ 31#5

theorem mem_of_evAt {α : Type} {tr : List (List α)} {p : Nat × Nat} {y : α}
    (h : evAt tr p = some y) : ∃ x ∈ tr, y ∈ x := by
  unfold evAt at h
  cases hp : tr[p.1]? with
  | none => rw [hp] at h; cases h
  | some x =>
    rw [hp] at h
    exact ⟨x, List.mem_of_getElem? hp, List.mem_of_getElem? h⟩

/-- **Private writes of labels without `relXW`.** -/
theorem privW_labs {Priv : Nat → Prop} {L : List Lab}
    (h : ∀ p y, evAt (evTr L) p = some y → y.k.dir = .W → Priv y.addr.toNat)
    (hk : ∀ l ∈ L, ∀ e ∈ l.evs, e.k ≠ .relXW) : PrivW Priv (evTr L) := fun p y hy hd => by
  refine ⟨h p y hy hd, ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_of_evAt hy
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact hk l hl y hyx

/-- A step at an error has only barrier events. -/
theorem stepEvs_err {s : ArmState} (h : read_err s ≠ .None) : ∀ e ∈ stepEvs s, e.k = .dmb := by
  unfold stepEvs
  split
  · rw [if_neg h]
    intro e he
    unfold errEvs at he
    split at he
    · split at he
      · simp only [List.mem_singleton] at he; subst he; rfl
      · exact absurd he List.not_mem_nil
    · exact absurd he List.not_mem_nil
  · intro e he; exact absurd he List.not_mem_nil

/-- An `ldaxr` with a base other than `sp`, without error, reads with an `acqXR` event. -/
theorem stepEvs_ldx {s : ArmState} {rn : BitVec 5} {sz : BitVec 2}
    (hc : cls s = .ldx true rn sz) (hrn : rn ≠ 31#5) (herr : read_err s = .None) :
    ∃ e ∈ stepEvs s, e.k = .acqXR := by
  unfold cls at hc
  cases hd : decodeAt s with
  | none => rw [hd] at hc; cases hc
  | some ai =>
    rw [hd] at hc
    cases ai with
    | LDST i =>
      cases i with
      | Reg_exclusive i =>
        simp only at hc
        split at hc
        · split at hc <;> cases hc
        · rename_i hord
          split at hc
          · rename_i hL
            simp only [Cls.ldx.injEq, decide_eq_true_eq] at hc
            obtain ⟨ho0, hRn, -⟩ := hc
            unfold stepEvs
            rw [hd]
            dsimp only
            rw [if_pos herr]
            dsimp only [instEvs, exclEvs]
            rw [if_neg (by rintro ⟨h, -⟩; exact hrn (hRn ▸ h)), if_pos hL]
            exact ⟨_, List.mem_singleton_self _, by simp [exclKind, hL, hord, ho0]⟩
          · cases hc
      | _ => cases hc
    | BR i =>
      cases i <;> simp only at hc
      all_goals (try split at hc) <;> (try split at hc) <;> cases hc
    | _ => cases hc

theorem reread1_k (m : Memory) (e : Ev) : (ArmPrecise.reread1 m e).k = e.k := by
  unfold ArmPrecise.reread1; split <;> rfl

/-- The invariant of `xClosed_mon`: an armed monitor follows an `acqXR` of the trace so far, or
the thread is at an error. -/
def MonInv (A : List (List Ev)) (t : ArmState × Mon) : Prop :=
  t.2.isSome → (∃ a x, evAt A a = some x ∧ x.k = .acqXR) ∨ read_err t.1 ≠ .None

theorem read_err_setMem (m : Memory) (s : ArmState) : read_err (setMem m s) = read_err s :=
  r_setMem _ _ _

/-- **Runs from the open monitor on programs whose load exclusives acquire are
exclusive-closed** (module doc), with the trace `A` before. -/
theorem xClosed_mon {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {π : Arm.Program}
    (hf : ∀ s, s.program = π → (f s).program = π)
    (he : ∀ s, s.program = π → read_err s ≠ .None → read_err (f s) ≠ .None)
    (hx : ∀ s, s.program = π → LdxAcq s) :
    ∀ {t t' : ArmState × Mon} {ls : List Lab} (A : List (List Ev)), t.1.program = π →
      PRun Policy.arm f ok t ls t' → CallCompose.XClosed A → MonInv A t →
      CallCompose.XClosed (A ++ evTr ls)
  | _, _, _, A, _, .nil, hA, _ => by simpa [evTr] using hA
  | (s, mon), _, l :: ls, A, hπ, .cons (t1 := t1) hs hp _ hr, hA, hI => by
    simp only at hπ
    have hm : ∀ m, (setMem m s).program = π := fun m => by rw [setMem_program]; exact hπ
    -- an `acqXR` of `A` stays one of `A ++ [l.evs]`
    have hlift : ∀ a x, evAt A a = some x → evAt (A ++ [l.evs]) a = some x := fun a x h => by
      rw [evAt_append_lt _ _ (evAt_lt h)]; exact h
    have hA1 : CallCompose.XClosed (A ++ [l.evs]) := by
      intro b y hy hk
      by_cases hb : b.1 < A.length
      · rw [evAt_append_lt _ _ hb] at hy
        obtain ⟨a, x, hx', hxk, hab⟩ := hA b y hy hk
        exact ⟨a, x, hlift a x hx', hxk, hab⟩
      · rw [evAt_append_ge _ _ (by omega)] at hy
        obtain ⟨z, hz, hyz⟩ := mem_of_evAt hy
        simp only [List.mem_singleton] at hz
        subst hz
        cases hs with
        | @exec _ _ evs hk' _ _ hsucc =>
          have hcl := hk'.1 y hyz
          rw [hk] at hcl
          have hstx : ∃ rs rn, cls s = .stx true rs rn := by
            cases hc : cls s <;> rw [hc] at hcl <;> simp [Cls.kind, AKind.dir] at hcl
            rename_i rel rs rn
            cases rel
            · simp [Cls.kind, AKind.dir] at hcl
            · exact ⟨rs, rn, rfl⟩
          obtain ⟨rs, rn, hc⟩ := hstx
          have hmon : mon.isSome := hsucc _ _ _ hc
          have herr : read_err s = .None := by
            refine Classical.byContradiction fun hne => ?_
            rcases hp with h | ⟨m, hm'⟩
            · cases h
            · simp only at hm'
              rw [hm', ArmPrecise.stepEvs_setMem] at hyz
              obtain ⟨e0, he0, hk0, -, -⟩ := mem_reread hyz
              have := stepEvs_err hne e0 he0
              rw [hk, this] at hk0; cases hk0
          rcases hI hmon with ⟨a, x, hx', hxk⟩ | h
          · refine ⟨a, x, hlift a x hx', hxk, .inl ?_⟩
            have := evAt_lt hx'; omega
          · exact absurd herr h
        | xfail => exact absurd hyz List.not_mem_nil
    have hI1 : t1.1.program = π ∧ MonInv (A ++ [l.evs]) t1 := by
      cases hs with
      | @exec _ _ evs _ _ _ _ =>
        refine ⟨hf _ (hm _), fun hsome => ?_⟩
        simp only at hsome ⊢
        have hkeep : MonInv A (s, mon) → mon.isSome →
            (∃ a x, evAt (A ++ [evs]) a = some x ∧ x.k = .acqXR) ∨
              read_err (f (setMem (applyR evs s.mem) s)) ≠ .None := fun hI' hs' => by
          rcases hI' hs' with ⟨a, x, hx', hxk⟩ | h
          · exact .inl ⟨a, x, hlift a x hx', hxk⟩
          · exact .inr (he _ (hm _) (by rw [read_err_setMem]; exact h))
        cases hc : cls s with
        | ldx acq rn sz =>
          obtain ⟨rfl, hrn⟩ := hx s hπ _ _ _ hc
          by_cases herr : read_err s = .None
          · left
            obtain ⟨e0, he0, hk0⟩ := stepEvs_ldx hc hrn herr
            rcases hp with h | ⟨m, hm'⟩
            · cases h
            · simp only at hm'
              have hmem : ArmPrecise.reread1 m e0 ∈ evs := by
                rw [hm', ArmPrecise.stepEvs_setMem]
                exact List.mem_map_of_mem he0
              obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hmem
              refine ⟨(A.length, i), ArmPrecise.reread1 m e0, ?_, by rw [reread1_k, hk0]⟩
              rw [evAt_append_ge _ _ (Nat.le_refl _)]
              simp [evAt, ← hei, hi]
          · exact .inr (he _ (hm _) (by rw [read_err_setMem]; exact herr))
        | stx => rw [hc] at hsome; simp [monAfter] at hsome
        | clrex => rw [hc] at hsome; simp [monAfter] at hsome
        | plain => rw [hc] at hsome; exact hkeep hI hsome
        | ldar => rw [hc] at hsome; exact hkeep hI hsome
        | stlr => rw [hc] at hsome; exact hkeep hI hsome
        | dmb => rw [hc] at hsome; exact hkeep hI hsome
      | xfail =>
        refine ⟨by simp only; rw [failState_program]; exact hπ, fun h => ?_⟩
        simp at h
    have := xClosed_mon hf he hx (A ++ [l.evs]) hI1.1 hr hA1 hI1.2
    simpa [evTr, List.append_assoc] using this

/-- **`xClosed_mon` from the open monitor.** -/
theorem xClosed_mon0 {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {π : Arm.Program}
    (hf : ∀ s, s.program = π → (f s).program = π)
    (he : ∀ s, s.program = π → read_err s ≠ .None → read_err (f s) ≠ .None)
    (hx : ∀ s, s.program = π → LdxAcq s) {s : ArmState} {t' : ArmState × Mon} {ls : List Lab}
    (hπ : s.program = π) (hr : PRun Policy.arm f ok (s, none) ls t') :
    CallCompose.XClosed (evTr ls) := by
  simpa using xClosed_mon hf he hx [] hπ hr CallCompose.xClosed_nil (fun h => by simp at h)

/-- The machine with hooks keeping the error keeps it. -/
theorem armStepX_err {X : ExtSem} {H : ArmHooks} {fa : FnAsm}
    (hH : ∀ d s, read_err s ≠ .None → read_err (H.call d s) ≠ .None)
    (hT : ∀ n r s, read_err s ≠ .None → read_err (H.tls n r s) ≠ .None) (s : ArmState)
    (h : read_err s ≠ .None) : read_err (ArmStepX X H fa s) ≠ .None := by
  unfold ArmStepX
  dsimp only
  split
  · exact hH _ _ h
  · exact hH _ _ h
  all_goals first
    | exact hT _ _ _ h
    | (rw [stepi_err h]; exact h)
    | (simp only [read_err] at h ⊢
       repeat rw [Arm.r_of_w_different (by simp)]
       exact h)

/-! ## The callee contract from the open monitor -/

/-- **`funReal_callee` entered with the open monitor** (its premise on the runs from there). -/
theorem funReal_callee0 {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    (hc : CompiledE env p RA cs) (ext : List (Clif.Frame × List Clif.ValueId))
    {M : ArmState → ArmState} (hM : ∀ s, s.program = RA.s0.program → M s = RA.step s)
    (hP : ∀ s, s.program = RA.s0.program → (RA.step s).program = RA.s0.program)
    (hX : ∀ ls t', PRun Policy.arm RA.step (OkPriv RA) (RA.s0, none) ls t' →
      CallCompose.XClosed (evTr ls)) :
    CallCompose.FunReal env p (PrivA RA) M (OkPriv RA) (fun _ _ _ _ => False)
      (CalleeEnd env p RA ext) (RA.s0, none) (.run (ClifLift.pushC ext cs)) := by
  intro ls t' hr
  have hr' := prun_transfer (π := RA.s0.program) hM hP rfl hr
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := thread_compiled_entry hc hr'
  obtain ⟨trS', t2, hrun2, hpre, hdrop, -, hrunE, hretE⟩ := ClifLift.crun_pushC (ext := ext) hrun
  obtain ⟨v, hv, -⟩ := CallCompose.take_prun hr' k
  refine ⟨k, t2, ⟨hk, trS', ψ, hrun2, hX _ _ hv, refines_prefix_nil href hpre hdrop⟩, ?_⟩
  rcases hend with h | h | h
  · exact .inl h
  · right; left; right
    cases t with
    | run s' =>
      obtain ⟨rfl, -⟩ := hrunE s' rfl
      exact ⟨s', rfl, .inl h⟩
    | ret w =>
      obtain ⟨s', rfl, hc'⟩ := hretE w rfl
      exact ⟨s', rfl, .inr ⟨w, hc'⟩⟩
  · exact .inr (.inl (.inl h))

/-- **The callee contract of a compiled callee whose load exclusives acquire** (e.g. with
`atomic_rmw`/`atomic_cas` loops; `xClosed_mon`), entered with the open monitor: the machine keeps
the program and the error, and every state holding the program satisfies `LdxAcq`. -/
theorem funReal_calleeX {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    (hc : CompiledE env p RA cs) (ext : List (Clif.Frame × List Clif.ValueId))
    {M : ArmState → ArmState} (hM : ∀ s, s.program = RA.s0.program → M s = RA.step s)
    (hP : ∀ s, s.program = RA.s0.program → (RA.step s).program = RA.s0.program)
    (hE : ∀ s, s.program = RA.s0.program → read_err s ≠ .None → read_err (RA.step s) ≠ .None)
    (hx : ∀ s, s.program = RA.s0.program → LdxAcq s) :
    CallCompose.FunReal env p (PrivA RA) M (OkPriv RA) (fun _ _ _ _ => False)
      (CalleeEnd env p RA ext) (RA.s0, none) (.run (ClifLift.pushC ext cs)) :=
  funReal_callee0 hc ext hM hP fun _ _ hr => xClosed_mon0 hP hE hx rfl hr

end Concurrency.CallSeg
