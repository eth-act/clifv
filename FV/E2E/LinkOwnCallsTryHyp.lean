import FV.E2E.LinkOwnCallsTry

/-!
# `TryRunHyp`: a `try_call`'s `lower_branch` run

Only the `try_call` rules match a `try_call`'s data (`tryUnmatchable`, `tryIndUnmatchable`), so
a run that commits to a rule emits exactly that rule's code (`try_bl_rel`, `try_got_rel`,
`try_ind_rel`): stores, the GOT load, then the call. (A run that commits to no rule returns no
value and keeps the empty code: `TryRunHyp` asks for a returned value, as the driver's
`try_call` run has one, `lowTerm_spec`.)
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp
  Isle.Aarch64

set_option maxRecDepth 100000

theorem tryRun_final {f : Clif.Function} {t : Clif.Terminator} {N : Nat} {s0 s' : LState}
    (h0 : s0.emitted = #[]) (E : List (Nat × Nat × Nat)) (pre : List MInst) (cl : CallInfo)
    (he : s'.emitted = s0.emitted ++ (E.map argStore ++ pre ++ [MInst.call cl]).toArray)
    (hpre : ∀ m ∈ pre, isCallB m = false)
    (hrc : TryRunCall f t N (E.map argStore ++ pre ++ [MInst.call cl]) cl) :
    ∃ (ms : List MInst) (c : CallInfo), s'.emitted = (ms ++ [MInst.call c]).toArray ∧
      NoTry ms ∧ NoCalls ms ∧ TryRunCall f t N (ms ++ [MInst.call c]) c := by
  refine ⟨E.map argStore ++ pre, cl, by rw [he, h0]; simp, fun c ti hm => ?_, fun c hm => ?_, hrc⟩
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, he'⟩ := List.mem_map.mp hm
      cases he'
    · have := hpre _ hm
      simp [isCallB] at this
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, he'⟩ := List.mem_map.mp hm
      cases he'
    · have := hpre _ hm
      simp [isCallB] at this

theorem lower_branch_len : (program.rulesOf 687).length ≤ 1000 := by
  rw [data_program.r687]
  decide

/-- **`TryRunHyp`.** -/
theorem tryRunHyp : TryRunHyp := by
  intro f ctx ranges st0 _ hs ha hb ti t et data sig items lo trs st1 targets out s' tr _ hph het
    hB hd he hlo htr h
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  have hlo1 := (tryRegsOf_mono htr).1
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  have hlen := lower_branch_len
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  rcases internal_cases (cfg := {}) rfl data_program.t687 term_687_kind rfl happ with
    ⟨hr, -⟩ | ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, hnm, hmatch, heval⟩
  · cases hr
  · have hm1 : 1000 ≤ m := by omega
    rcases het with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · cases hroot : tryRootRule rl with
      | false =>
        exact absurd hmatch (tryUnmatchable rl hrl hroot f _ hctx' ti fn args et data targets hd hi
          {} m _ env _)
      | true =>
        simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        rcases hroot with e | e
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2542 (by rw [e]; rfl)] at hmatch heval
          obtain ⟨E, cl, he', hrc, -⟩ := try_bl_rel (N := ctx.valDef.size) data_program
            tryData_program hctx' ha hd he hi htr' rfl hm1 (by omega) hmatch heval
          exact tryRun_final rfl E [] cl he' (fun _ h => by cases h) hrc
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2551 (by rw [e]; rfl)] at hmatch heval
          obtain ⟨E, nm, L, K, he', hrc, -⟩ := try_got_rel (N := ctx.valDef.size)
            (st := { st1 with emitted := #[] }) data_program
            tryData_program hctx' ha hd he hi htr' rfl hm1 (by omega)
            (show ctx.valDef.size ≤ st1.nextVreg by omega) (Nat.le_refl _) hmatch heval
          exact tryRun_final rfl E _ _ he' (by simp [isCallB]) hrc
    · cases hroot : tryIndRootRule rl with
      | false =>
        exact absurd hmatch (tryIndUnmatchable rl hrl hroot f _ hctx' ti callee args et data
          targets hd hi {} m _ env _)
      | true =>
        simp only [tryIndRootRule, beq_iff_eq] at hroot
        rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2561 (by rw [hroot]; rfl)] at hmatch heval
        obtain ⟨E, cl, he', hrc⟩ := try_ind_rel (N := ctx.valDef.size) data_program
          tryData_program indData_program tryIndData_program hctx' hd he hi htr' rfl hm1
          (by omega) hmatch heval
        exact tryRun_final rfl E [] cl he' (fun _ h => by cases h) hrc

end E2E.LinkCheck
