import FV.Backend.Proof.DeadCleanupLive
import FV.Backend.Proof.SpillInvariant

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Spill

private theorem availInst_frame (i : MInst) (A : Nat → Bool) (n : Nat)
    (hn : n ∉ defs i) : availInst i A n = A n := by
  unfold availInst
  cases hop : i.operands with
  | error e => rfl
  | ok ops =>
    have hnot : ¬(ops.toList.filter (·.kind == .def)).any (·.vreg == n) = true := by
      intro h
      obtain ⟨o, ho, he⟩ := List.any_eq_true.mp h
      apply hn
      simp only [defs, hop]
      exact List.mem_map.mpr ⟨o, ho, by simpa using he⟩
    dsimp only
    rw [ite_eq_right hnot]

/-- Availability agrees after a retained instruction on the live continuation. -/
theorem availInst_agree (nregs : Nat) (i : MInst) (live : List Nat) (A B : Nat → Bool)
    (h : Agree (uses nregs i ++ live.filter (fun n => !(defs i).contains n)) A B) :
    Agree live (availInst i A) (availInst i B) := by
  intro n hn
  cases hop : i.operands with
  | error e =>
    simpa [availInst, hop] using h n (by simp [uses, defs, hop, hn])
  | ok ops =>
    by_cases hd : (ops.toList.filter (·.kind == .def)).any (·.vreg == n) = true
    · simp [availInst, hop, hd]
    · have hnDef : n ∉ defs i := by
        intro hm
        simp only [defs, hop, List.mem_map] at hm
        obtain ⟨o, ho, he⟩ := hm
        apply hd
        exact List.any_eq_true.mpr ⟨o, ho, by simp [he]⟩
      rw [availInst_frame i A n hnDef, availInst_frame i B n hnDef]
      exact h n (List.mem_append_right _ (List.mem_filter.mpr ⟨hn, by simp [hnDef]⟩))

/-- Skipping a dead definition does not change availability on the live remainder. -/
theorem discard_availInst_agree {i : MInst} {live : List Nat}
    (hd : discard i live = true) (A : Nat → Bool) :
    Agree live (availInst i A) A := by
  intro n hn
  apply availInst_frame
  intro hdef
  exact discard_dead hd n hdef hn

/-- Availability needed by the instruction's actual operand reads. -/
def ReadsReady (i : MInst) (A : Nat → Bool) : Prop :=
  match i.operands with
  | .error _ => True
  | .ok ops => ∀ o ∈ ops.toList, o.kind = .use → A o.vreg = true

/-- Every retained read is available during a straight-line block walk. -/
def AvailRunReady : List MInst → (Nat → Bool) → Prop
  | [], _ => True
  | i :: ms, A => ReadsReady i A ∧ AvailRunReady ms (availInst i A)

private theorem readsReady_agree {nregs : Nat} {i : MInst} {live : List Nat}
    {A B : Nat → Bool}
    (ha : Agree (uses nregs i ++ live.filter (fun n => !(defs i).contains n)) A B)
    (hr : ReadsReady i A) : ReadsReady i B := by
  unfold ReadsReady at hr ⊢
  cases hop : i.operands with
  | error e => trivial
  | ok ops =>
    simp only [hop] at hr ⊢
    intro o ho hu
    rw [← ha o.vreg (by simp [uses, hop, List.mem_map, List.mem_filter]; exact Or.inl ⟨o, ⟨by simpa using ho, by simp [hu]⟩, rfl⟩)]
    exact hr o ho hu

/-- Cleanup preserves the availability of every surviving read and agrees
at the block boundary on the registers the next block may read. -/
theorem scan_availability (nregs : Nat) (ms : List MInst) (exit : List Nat)
    (A B : Nat → Bool) (ha : Agree (scan nregs ms exit).2 A B)
    (hr : AvailRunReady ms A) :
    AvailRunReady (scan nregs ms exit).1 B ∧
      Agree exit (ms.foldl (fun A i => availInst i A) A)
        ((scan nregs ms exit).1.foldl (fun B i => availInst i B) B) := by
  induction ms generalizing A B with
  | nil => exact ⟨trivial, ha⟩
  | cons i ms ih =>
    obtain ⟨hread, hrest⟩ := hr
    by_cases hd : discard i (scan nregs ms exit).2 = true
    · simp only [scan, hd, ↓reduceIte] at ha ⊢
      have hstep : Agree (scan nregs ms exit).2 (availInst i A) B := by
        intro n hn
        exact (discard_availInst_agree hd A n hn).trans (ha n hn)
      simpa only [List.foldl_cons] using ih (availInst i A) B hstep hrest
    · simp only [scan, hd, ↓reduceIte] at ha ⊢
      obtain ⟨hnew, hout⟩ := ih (availInst i A) (availInst i B)
        (availInst_agree nregs i _ A B ha) hrest
      exact ⟨⟨readsReady_agree ha hread, hnew⟩, hout⟩

theorem availRunReady_iff (ms : List MInst) (A : Nat → Bool) :
    AvailRunReady ms A ↔
      ∀ k i ops, ms[k]? = some i → i.operands = .ok ops →
        ∀ o ∈ ops.toList, o.kind = .use →
          (ms.take k).foldl (fun A i => availInst i A) A o.vreg = true := by
  induction ms generalizing A with
  | nil => simp [AvailRunReady]
  | cons i ms ih =>
    constructor
    · intro h k j ops hj hops o ho hu
      obtain ⟨hread, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst j
        simpa only [List.take_zero, List.foldl_nil] using
          (show ∀ o ∈ ops.toList, o.kind = .use → A o.vreg = true from
            by simpa [ReadsReady, hops] using hread) o ho hu
      | succ k =>
        have ht := (ih (availInst i A)).mp hrest k j ops hj hops o ho hu
        simpa only [List.take_succ_cons, List.foldl_cons] using ht
    · intro h
      refine ⟨?_, (ih (availInst i A)).mpr ?_⟩
      · unfold ReadsReady
        cases hops : i.operands with
        | error e => trivial
        | ok ops =>
          intro o ho hu
          exact h 0 i ops rfl hops o ho hu
      · intro k j ops hj hops o ho hu
        simpa only [List.take_succ_cons, List.foldl_cons] using
          h (k + 1) j ops hj hops o ho hu

/-- Every intermediate live register comes from a read in the block or its
boundary. This is the finite set used to restrict the old availability sets. -/
theorem scan_boundary_subset {nregs : Nat} {ms : List MInst} {exit : List Nat}
    (hu : ∀ i ∈ ms, ∀ n ∈ uses nregs i, n ∈ exit) :
    ∀ n ∈ (scan nregs ms exit).2, n ∈ exit := by
  induction ms with
  | nil => exact fun _ h => h
  | cons i ms ih =>
    have ht := ih (fun j hj => hu j (List.mem_cons_of_mem _ hj))
    simp only [scan]
    split
    · exact ht
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hu i (List.mem_cons_self ..) n hn
      · exact ht n (List.mem_filter.mp hn).1

/-! Joint non-vacuity: empty entry availability, an actual dead producer, and
a surviving return. No source or execution certificate is assumed. -/
example : ∃ ms : List MInst,
    AvailRunReady ms (fun _ => false) ∧
    Agree (scan 1 ms []).2 (fun _ => false) (fun _ => false) ∧
    (scan 1 ms []).1 = [.rets []] ∧
    AvailRunReady (scan 1 ms []).1 (fun _ => false) := by
  let m : MInst := .mov .size64 (.vreg 0 .int) .xzr
  have hm : m.operands = .ok #[⟨0, .int, .def, .late, .reg⟩] := rfl
  have hr : (MInst.rets []).operands = .ok #[] := rfl
  have hav : AvailRunReady [m, .rets []] (fun _ => false) := by
    simp [AvailRunReady, ReadsReady, hm, hr]
  have hag : Agree (scan 1 [m, .rets []] []).2 (fun _ => false) (fun _ => false) :=
    fun _ _ => rfl
  exact ⟨[m, .rets []], hav, hag, by decide,
    (scan_availability 1 [m, .rets []] [] _ _ hag hav).1⟩

end Backend.DeadCleanup
