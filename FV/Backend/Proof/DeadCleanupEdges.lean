import FV.Backend.Proof.DeadCleanupCFG

namespace Backend.DeadCleanup
open Backend.Proof

private theorem regNums_of_mapM : ∀ (rs : List Reg) (ns : List Nat),
    rs.mapM vregNum = .ok ns → ns = regNums rs := by
  intro rs
  induction rs with
  | nil => intro ns h; simpa [regNums, pure, Except.pure] using h.symm
  | cons r rs ih =>
    intro ns h
    cases r <;> simp only [List.mapM_cons, vregNum, bind, Except.bind,
      pure, Except.pure] at h
    all_goals try { cases h }
    rename_i n cls
    cases hm : rs.mapM vregNum with
    | error e => simp [hm] at h
    | ok rest =>
      simp only [hm, Except.ok.injEq] at h
      subst ns
      simp only [regNums, List.filterMap_cons]
      congr 1
      exact ih rest hm

private theorem lookup_snd_mem {ps xs : List Nat} {n x : Nat}
    (h : (ps.zip xs).lookup n = some x) : x ∈ xs := by
  induction ps generalizing xs with
  | nil => simp at h
  | cons p ps ih =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons] at h
      split at h
      · cases h; simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- Edge copies read only original outgoing arguments, which remain live on
all boundaries. The target's parameters and branch arguments are unchanged. -/
theorem clean_edge {V : Type} {vc : VCode} {b s : Nat} {vb sb : VBlock}
    (hb : vc.blocks[b]? = some vb) (hs : vc.blocks[s]? = some sb)
    {a c a' : Nat → V} (ha : Agree (exitLive vc 0 vb) a c)
    (he : edgeEnv vc b s a = some a') :
    ∃ c', edgeEnv (clean vc) b s c = some c' ∧ Agree (exitLive vc 0 sb) a' c' := by
  simp only [edgeEnv, hb, hs, bind, Option.bind] at he
  split at he
  · rename_i hsz
    cases hp : sb.params.toList.mapM vregNum with
    | error e => simp [hp, Except.toOption] at he
    | ok ps =>
      cases hx : vb.branchArgs.toList.mapM vregNum with
      | error e => simp [hp, hx, Except.toOption] at he
      | ok xs =>
        simp only [hp, hx, Except.toOption, pure,
          Option.some.injEq] at he
        subst a'
        refine ⟨parCopyEnv c ps xs, ?_, ?_⟩
        · simp [edgeEnv, clean_block hb, clean_block hs, cleanBlock, hsz, hp, hx, Except.toOption]
        · intro n hn
          simp only [parCopyEnv]
          cases hl : (ps.zip xs).lookup n with
          | none => exact ha n hn
          | some x =>
            apply ha x
            have hx' : x ∈ regNums vb.branchArgs.toList := by
              rw [← regNums_of_mapM _ _ hx]
              exact lookup_snd_mem hl
            exact blockUses_exit (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))
              (List.mem_append_left _ hx') 0 vb
  · simp at he

/-! Non-vacuity: copy a real outgoing argument into the next block's parameter. -/
example : ∃ vc : VCode, ∃ a' : Nat → Nat,
    edgeEnv (clean vc) 0 1 (fun _ => 7) = some a' ∧
      Agree (exitLive vc 0 vc.blocks[1]!) (fun _ => 7) a' := by
  let vc : VCode := ⟨"cleanup_edge",
    #[⟨0, #[deadMvn, .jump 1], #[], #[.vreg 1 .int]⟩,
      ⟨1, #[.rets [(.vreg 0 .int, .x 0)]], #[.vreg 0 .int], #[]⟩],
    #[.int, .int, .int], 0, 0, #[]⟩
  have he : edgeEnv vc 0 1 (fun _ => (7 : Nat)) = some (fun _ => 7) := by
    simp [edgeEnv, vc, vregNum, List.mapM_cons, bind, Except.bind,
      pure, Except.pure, Except.toOption, Option.bind]
    funext n
    by_cases hn : n = 0 <;> simp [parCopyEnv, hn]
  obtain ⟨a', ha, heq⟩ := clean_edge (vc := vc) (b := 0) (s := 1)
    (show vc.blocks[0]? = some vc.blocks[0]! from rfl)
    (show vc.blocks[1]? = some vc.blocks[1]! from rfl) (fun _ _ => rfl) he
  exact ⟨vc, a', ha, heq⟩

end Backend.DeadCleanup
