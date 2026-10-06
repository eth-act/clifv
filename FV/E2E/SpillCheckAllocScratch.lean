import FV.Backend.RegallocCheck

open Backend

example (a : Array (Option Nat)) (x : Option Nat) (i : Nat) (h : (x, i) ∈ a.zipIdx.toList) : a[i]? = some x := by
  rw [Array.toList_zipIdx] at h
  exact List.mem_zipIdx_iff_getElem?.mp h

theorem mapM_okL {α β : Type} (f : α → Except String β) : ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = .ok y) → ∃ ys, l.mapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_okL f l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

example {α β : Type} (l : Array α) (f : α → Except String β) (h : ∀ x ∈ l.toList, ∃ y, f x = .ok y) : ∃ ys, l.mapM f = .ok ys := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨ys, hys⟩ := mapM_okL f l.toList h
  exact ⟨ys.toArray, by rw [hys]; rfl⟩
