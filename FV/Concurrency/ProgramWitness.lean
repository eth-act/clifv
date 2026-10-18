import FV.Concurrency.ProgramE2E

/-!
# Non-vacuity of the program level (T2e, #303)

* `mp_replay`: message passing, `x = 1 (plain); y = 1 (atomic) ‖ r1 = y (atomic); r2 = x (plain)`
  with `r1 = r2 = 1`, as an execution of a toy thread semantics (a thread runs its given steps):
  every premise of `Prog.replay` holds (`mp_hyp`; SC by a rank certificate), and the replayed
  run of the interleaving machine ends with `x = y = 1` in memory.
* `ret_correct`: `ProgE2E.program_correct` for two CLIF threads that return and an Arm execution of
  two threads; every premise holds, the race-freedom premise is proven over all executions of the
  CLIF program (`ret_raceFree`), and the conclusion gives the run of the multi-threaded `Clif.run`
  in which both threads return.
-/

namespace Concurrency.ProgWitness

open Rel Prog ClifThread ProgE2E

/-! ## Replay: message passing -/

/-- An event of the toy semantics. -/
abbrev E := Ev SKind BVal

def wx : E := ⟨.naW, .W, 0, 1, [some 1]⟩
def wy : E := ⟨.scW, .W, 8, 1, [some 1]⟩
def ry : E := ⟨.scR, .R, 8, 1, [some 1]⟩
def rx : E := ⟨.naR, .R, 0, 1, [some 1]⟩

/-- The threads' steps. -/
def steps : Nat → List (List E)
  | 0 => [[wx], [wy]]
  | 1 => [[ry], [rx]]
  | _ => []

/-- A thread runs its given steps. -/
def T : TSem (List (List E)) SKind BVal := fun s evs s' => s = evs :: s'

def P : Traces (List (List E)) SKind BVal := ⟨2, steps, fun i j => (steps i).drop j⟩

def locs : List (Nat × Nat) := [(0, 1), (8, 1)]

def M0 : Bytes := fun _ => some 0

def rf (a b : PEv) : Prop := (a = .thr 0 1 0 ∧ b = .thr 1 0 0) ∨ (a = .thr 0 0 0 ∧ b = .thr 1 1 0)

def co (a b : PEv) : Prop := (a = .init 0 ∧ b = .thr 0 0 0) ∨ (a = .init 1 ∧ b = .thr 0 1 0)

def rmw (_ _ : PEv) : Prop := False

abbrev X := P.exec locs rf co rmw

theorem evAt_cases {i j k : Nat} {x : E} (h : P.evAt (.thr i j k) = some x) :
    (i = 0 ∧ j = 0 ∧ k = 0 ∧ x = wx) ∨ (i = 0 ∧ j = 1 ∧ k = 0 ∧ x = wy) ∨
      (i = 1 ∧ j = 0 ∧ k = 0 ∧ x = ry) ∨ (i = 1 ∧ j = 1 ∧ k = 0 ∧ x = rx) := by
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> rcases k with _ | k <;>
    simp [Traces.evAt, P, steps] at h <;> simp [h]

/-- The events (positions with an event, and the initial writes). -/
def evs : List PEv := [.init 0, .init 1, .thr 0 0 0, .thr 0 1 0, .thr 1 0 0, .thr 1 1 0]

theorem mem_evs {e : PEv} (h : X.dir e ≠ .F) : e ∈ evs := by
  cases e with
  | init q =>
    rcases q with _ | _ | q <;> simp [evs]
    simp [Traces.exec, locs] at h
  | thr i j k =>
    rcases hx : P.evAt (.thr i j k) with _ | x
    · simp [Traces.exec, hx] at h
    · rcases evAt_cases hx with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ |
        ⟨rfl, rfl, rfl, -⟩ <;> simp [evs]

theorem wf : X.Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir a b h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rf_loc a b h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rf_func a a' b h1 h2 := by
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      first | rfl | cases h
  rf_total b hb := by
    have := mem_evs (e := b) (by rw [hb]; decide)
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | exact ⟨_, .inl ⟨rfl, rfl⟩⟩
      | exact ⟨_, .inr ⟨rfl, rfl⟩⟩
  co_dir a b h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  co_loc a b h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  co_irrefl a h := by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
  co_trans a b c h1 h2 := by
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  co_total a b ha hb hl hne := by
    have h1 := mem_evs (e := a) (by rw [ha]; decide)
    have h2 := mem_evs (e := b) (by rw [hb]; decide)
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact absurd ha (by decide)
      | exact absurd hb (by decide)
      | exact absurd hl (by decide)
      | exact .inl (.inl ⟨rfl, rfl⟩)
      | exact .inl (.inr ⟨rfl, rfl⟩)
      | exact .inr (.inl ⟨rfl, rfl⟩)
      | exact .inr (.inr ⟨rfl, rfl⟩)
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

/-- The interleaving rank of the events. -/
def rank : PEv → Nat
  | .init q => q
  | .thr i j _ => 2 + 2 * i + j

theorem sc : X.SC := by
  refine sc_of_rank_on wf (· ∈ evs) rank ?_ ?_ ?_
  · intro a b h
    exact ⟨mem_evs (wf.com_notF h).1, mem_evs (wf.com_notF h).2⟩
  · intro a b ha hb h
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Traces.exec, PEv.po, rank]
  · intro a b h
    rcases h with h | h | ⟨w, h1, h2⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

theorem mp_hyp : ReplayHyp bytesI T P locs rf co rmw M0 [] where
  runs i hi j hj := by
    show (steps i).drop j = (steps i)[j] :: (steps i).drop (j + 1)
    exact List.drop_eq_getElem_cons hj
  wf := wf
  sc := sc
  atom _ _ h := h.elim
  val w r h := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  shape := ⟨fun i hi j hj => .inl (by
      have hi' : i < 2 := hi
      rcases i with _ | _ | i
      · rcases j with _ | _ | j <;> simp [P, steps] at hj ⊢ <;> omega
      · rcases j with _ | _ | j <;> simp [P, steps] at hj ⊢ <;> omega
      · omega), fun _ _ h => h.elim⟩
  ov a b ha hb := by
    have h1 := mem_evs ha
    have h2 := mem_evs hb
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  init w q h := by rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  wok i j k x hx _ := by
    rcases evAt_cases hx with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl

/-- **Replay of message passing**: the SC execution is a run of the interleaving machine, and the
final memory holds `x = 1` and `y = 1`. -/
theorem mp_replay : ∃ M', MRun bytesI T (fun i => P.st i 0, M0)
      (fun i => P.st i (if i < P.n then (P.tr i).length else 0), M') ∧
      getB M' 0 1 = [some 1] ∧ getB M' 8 1 = [some 1] := by
  obtain ⟨M', hrun, hmem⟩ := replay (H := mp_hyp)
  refine ⟨M', hrun, ?_, ?_⟩
  · have := hmem (.thr 0 0 0) (by decide) (by
      intro w' hw hl hne
      have := mem_evs (e := w') (by rw [hw]; decide)
      simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact .inl ⟨rfl, rfl⟩
        | exact absurd rfl hne
        | exact absurd hw (by decide)
        | exact absurd hl (by decide))
    exact this
  · have := hmem (.thr 0 1 0) (by decide) (by
      intro w' hw hl hne
      have := mem_evs (e := w') (by rw [hw]; decide)
      simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact .inr ⟨rfl, rfl⟩
        | exact absurd rfl hne
        | exact absurd hw (by decide)
        | exact absurd hl (by decide))
    exact this

/-! ## `program_correct`: two threads that return -/

/-- A CLIF thread about to `return` (no values). -/
def sR : Clif.State :=
  { frame := { func := default, regs := fun _ => none, slots := [], body := [], term := .ret [] },
    callers := [], mem := default }

def env0 : Clif.Env := {}
def p0 : Clif.Program := default

/-- Both threads start about to return. -/
def s0 : Nat → TState := fun _ => .run sR

theorem step_sR (B : Bytes) : res (Clif.step env0 p0 (withBytes sR B)) = some (.ret [], B) := rfl

theorem cstep_sR {evs : List (Ev SKind BVal)} {t' : TState} (h : CStep env0 p0 (.run sR) evs t') :
    evs = [] ∧ ∃ v, t' = .ret v := by
  obtain ⟨⟨hsh, -⟩, -, hfp⟩ := h
  have hevs : evs = [] := by
    simp only [evShape, sR, List.mem_singleton, List.map_eq_nil_iff] at hsh
    exact hsh
  subst hevs
  obtain ⟨t'', h1, h2⟩ := hfp (fun _ => none) trivial
  rw [step_sR] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  rw [← h1.1] at h2
  cases t' with
  | run s => simp [strip] at h2
  | ret v => exact ⟨rfl, v, rfl⟩

/-- **Race-freedom of the program over all its executions**: its threads have no memory events. -/
theorem ret_raceFree (M0 : Bytes) : RaceFreeProg env0 p0 2 s0 M0 := by
  intro P locs rf co rmw hn hs0 hruns _ _ _ _ a b ha _ hconf _
  exfalso
  -- every step of every thread has no event
  have hnil : ∀ i < P.n, ∀ j (hj : j < (P.tr i).length), (P.tr i)[j] = [] := by
    intro i hi j hj
    rcases j with _ | j
    · have h := hruns i hi 0 hj
      rw [hs0] at h
      exact (cstep_sR h).1
    · exfalso
      have h0 := hruns i hi 0 (by omega)
      rw [hs0] at h0
      obtain ⟨-, v, hv⟩ := cstep_sR h0
      have h1 := hruns i hi 1 (by omega)
      rw [hv] at h1
      rcases j with _ | j
      · exact h1
      · have h1' := hruns i hi (j + 1) (by omega)
        -- the thread returned at its first step and has no step after it
        have : ∀ m, 1 ≤ m → m < (P.tr i).length → ∃ v, P.st i m = .ret v := by
          intro m hm hml
          induction m with
          | zero => omega
          | succ m ih =>
            rcases m with _ | m
            · exact ⟨v, hv⟩
            · obtain ⟨v', hv'⟩ := ih (by omega) (by omega)
              have := hruns i hi (m + 1) (by omega)
              rw [hv'] at this; exact this.elim
        obtain ⟨v', hv'⟩ := this (j + 1) (by omega) (by omega)
        rw [hv'] at h1'; exact h1'
  have hda := hconf.2.2.1
  cases a with
  | init q => exact ha q rfl
  | thr i j k =>
    rcases hx : P.evAt (.thr i j k) with _ | x
    · exact hda (by simp [Traces.exec, hx])
    · obtain ⟨hi, hj, hk, -⟩ := Traces.evAt_some hx
      rw [hnil i hi j hj] at hk
      exact absurd hk (Nat.not_lt_zero _)

/-- The CLIF threads' traces: one step each, to the return. -/
def PC : Traces TState SKind BVal :=
  ⟨2, fun _ => [[]], fun _ j => if j = 0 then .run sR else .ret []⟩

/-- The Arm threads (no steps; any machine). -/
def PA : Traces AState AKind BVal := ⟨2, fun _ => [], fun _ _ => (Arm.stepi, Arm.ArmState.default, none)⟩

def none2 (_ _ : PEv) : Prop := False

theorem PA_evAt (e : PEv) : PA.evAt e = none := by
  cases e <;> simp [Traces.evAt, PA]

theorem PC_evAt (e : PEv) : PC.evAt e = none := by
  cases e with
  | init => rfl
  | thr i j k =>
    simp only [Traces.evAt, PC]
    by_cases hi : i < 2 <;> simp only [hi, ite_true, ite_false]
    rcases j with _ | j <;> simp

theorem PA_dir (e : PEv) : (PA.exec [] none2 none2 none2).dir e = .F := by
  cases e with
  | init => rfl
  | thr i j k => simp [Traces.exec, PA_evAt]

theorem wfA : (PA.exec [] none2 none2 none2).Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir _ _ h := h.elim
  rf_loc _ _ h := h.elim
  rf_func _ _ _ h := h.elim
  rf_total b h := absurd h (by rw [PA_dir]; decide)
  co_dir _ _ h := h.elim
  co_loc _ _ h := h.elim
  co_irrefl _ h := h.elim
  co_trans _ _ _ h := h.elim
  co_total a _ h := absurd h (by rw [PA_dir]; decide)
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

theorem consA : Armv8.Consistent (PA.exec [] none2 none2 none2) (kindA PA) where
  internal a h := by
    obtain ⟨c, hc, -⟩ := plus_head h
    rcases hc with ⟨-, -, h, -⟩ | h
    · exact h (PA_dir _)
    · rcases h with h | h | ⟨_, h, -⟩ <;> exact h
  atomic _ _ h := h.elim
  external a h := by
    obtain ⟨c, hc, -⟩ := plus_head h
    have hk : ∀ e, kindA PA e = .plainW := fun e => by simp [kindA, PA_evAt]
    rcases hc with (⟨h, -⟩ | ⟨h, -⟩ | ⟨⟨_, h, -⟩, -⟩) | h | h
    · exact h
    · exact h
    · exact h
    · exact h
    · rcases h with ⟨f, -, hf, -⟩ | ⟨hl, -⟩ | ⟨ha, -⟩ | ⟨-, hl⟩
      · rw [hk] at hf; cases hf
      · rcases hl with hl | hl <;> rw [hk] at hl <;> cases hl
      · rcases ha with ha | ha <;> rw [hk] at ha <;> cases ha
      · rcases hl with hl | hl <;> rw [hk] at hl <;> cases hl

/-- The threads' outcome: the CLIF thread returned. -/
def Obs : Nat → AState → TState → Prop := fun _ _ t => t = .ret []

theorem realizes : Realizes PA [] (fun _ => none) none2 none2 none2 PC [] (fun _ => none) id Obs where
  threads := rfl
  valid e h := by
    cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  inj a b _ _ h := h
  po _ _ _ _ := Iff.rfl
  init q h := absurd h (Nat.not_lt_zero _)
  dir e h := by cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  loc e h := by cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  sz e h := by cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  val e h := by cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  kind e h := by cases e with
    | init q => exact absurd h (Nat.not_lt_zero _)
    | thr => simp [Valid, PC_evAt] at h
  rf_src _ _ _ h := h.elim
  shape := ⟨fun i _ j hj => .inl (by simp [PC] at hj ⊢), fun _ _ h => h.2.2.elim⟩
  obs i hi := rfl

theorem runsC : PC.Runs (CStep env0 p0) := by
  intro i _ j hj
  simp only [PC, List.length_singleton] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  show CStep env0 p0 (.run sR) [] (.ret [])
  exact ⟨⟨by simp [evShape, sR], fun e he => absurd he List.not_mem_nil⟩, ⟨fun _ => none, trivial⟩,
    fun B _ => ⟨.ret [], step_sR B, rfl⟩⟩

/-- **Non-vacuity of `program_correct`**: two threads that return; the multi-threaded `Clif.run`
reaches both threads returned. -/
theorem ret_correct : ∃ ts B, MTRun env0 p0 (s0, fun _ => none) (ts, B) ∧
    StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
    (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) := by
  obtain ⟨-, ts, B, h1, h2, -, h3⟩ := program_correct realizes wfA (ret_raceFree _)
    (fun i hi j hj => absurd hj (Nat.not_lt_zero _)) consA (fun _ _ h => h.elim)
    (fun a _ ha => absurd (PA_dir a) ha) (fun _ _ h => h.elim) runsC rfl (fun _ => rfl)
  exact ⟨ts, B, h1, h2, h3⟩

end Concurrency.ProgWitness
