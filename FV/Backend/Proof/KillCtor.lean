import FV.Backend.Proof.KillOfV
import FV.Backend.Proof.IselCovClean
import FV.Backend.Proof.LowerLoop

/-!
# The killed-vreg invariant of the ISLE interpreter: constants, data, extern helpers

For the value invariant `KP ctx lo s0 s`, the state invariant `IsK ctx lo s0 s` and the run
relation `RsK` of `KillBase`:

* `rsK_refl`, `rsK_trans`, `kp_mono` (a value stays `KP` along a run);
* constants (`kp_int`, `kp_bool`, `kp_prim`), data (`kp_mkData`, `kp_unData`);
* `kp_extract`: every extern extractor gives `KP` values (from the context fact `DataK`: the
  instruction data holds no register and no killing `MInst` data);
* `kp_ctor`: every extern constructor but `invalid_reg` (`Excl`) keeps the invariants; its
  result registers come from its arguments, fresh vregs and CLIF values' vregs (`ValRegK`), the
  instructions it emits kill nothing (`ofV_kill`), and only `gen_try_call_rets` puts the
  `try_call`'s registers in a call's defs (`gen_call_rets` is only used outside a `try_call`).

The context facts hold for the driver's contexts: `valRegK_of_build`, `valRegK_termCtx`,
`valRegK_tryCtx`, `dataK_of_build`, `dataK_termCtx`, `dataK_tryCtx`, `termData_kClean`,
`tryCallData_kClean`.
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Aarch64

/-! ## Lists of values -/

theorem mem_regsKL {r : Reg} : ∀ {vs : List V}, r ∈ regsKL vs ↔ ∃ w ∈ vs, r ∈ w.regsK
  | [] => by simp
  | v :: vs => by simp [mem_regsKL]

theorem mem_regsDL {r : Reg} : ∀ {vs : List V}, r ∈ regsDL vs ↔ ∃ w ∈ vs, r ∈ w.regsD
  | [] => by simp
  | v :: vs => by simp [mem_regsDL]

theorem kInL_eq_false : ∀ {vs : List V}, kInL vs = false ↔ ∀ w ∈ vs, w.kIn = false
  | [] => by simp
  | v :: vs => by simp [kInL_eq_false]

theorem killedL_append (a b : List MInst) : killedL (a ++ b) = killedL a ++ killedL b := by
  simp [killedL]

theorem killedL_nil_of {ms : List MInst} (h : ∀ m ∈ ms, unstored m = []) : killedL ms = [] := by
  simp only [killedL, List.flatMap_eq_nil_iff]
  exact h

theorem emittedSince_eq {s0 s : LState} {ms : List MInst} (h : s.emitted = s0.emitted ++ ms.toArray) :
    emittedSince s0 s = ms := by
  simp [emittedSince, h]

/-! ## The run relation -/

theorem rsK_refl (s : LState) : RsK s s :=
  ⟨Nat.le_refl _, [], by simp, by simp [killedL]⟩

theorem rsK_trans {s1 s2 s3 : LState} (h1 : RsK s1 s2) (h2 : RsK s2 s3) : RsK s1 s3 := by
  obtain ⟨l1, ms1, e1, k1⟩ := h1
  obtain ⟨l2, ms2, e2, k2⟩ := h2
  refine ⟨Nat.le_trans l1 l2, ms1 ++ ms2, by simp [e2, e1], ?_⟩
  intro k hk
  rw [killedL_append, List.mem_append] at hk
  rcases hk with hk | hk
  · have := k1 k hk; omega
  · have := k2 k hk; omega

/-- An allowed vreg stays allowed when the counter grows and the new kills are fresh. -/
theorem vOk_mono {nV lo hi hi' : Nat} {K K' : List Nat} {n : Nat} (h : VOk nV lo hi K n)
    (hnv : nV ≤ hi) (hle : hi ≤ hi') (hK : ∀ k ∈ K', k ∈ K ∨ hi ≤ k) : VOk nV lo hi' K' n := by
  obtain ⟨h1, h2⟩ := h
  have hlt : n < hi := by omega
  refine ⟨by omega, fun hn => ?_⟩
  rcases hK n hn with h3 | h3
  · exact h2 h3
  · omega

/-- The kills of a run from `s0` to `s'` through `s`: the earlier ones, then fresh ones. -/
theorem killed_step {s0 s s' : LState} {ms0 : List MInst} (h0 : s.emitted = s0.emitted ++ ms0.toArray)
    (h : RsK s s') : ∃ ms, emittedSince s0 s' = emittedSince s0 s ++ ms ∧
      s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ k ∈ killedL (emittedSince s0 s'), k ∈ killedL (emittedSince s0 s) ∨ s.nextVreg ≤ k := by
  obtain ⟨-, ms, e, hk⟩ := h
  have e' : s'.emitted = s0.emitted ++ (ms0 ++ ms).toArray := by simp [e, h0]
  refine ⟨ms, by rw [emittedSince_eq e', emittedSince_eq h0], e, ?_⟩
  intro k hk'
  rw [emittedSince_eq e', killedL_append, List.mem_append] at hk'
  rw [emittedSince_eq h0]
  rcases hk' with hk' | hk'
  · exact .inl hk'
  · exact .inr (hk k hk').1

/-- **A value stays `KP` along a run.** -/
theorem kp_mono {ctx : Ctx} {lo : Nat} {s0 s s' : LState} {v : V} (hI : IsK ctx lo s0 s)
    (hr : RsK s s') (hv : KP ctx lo s0 s v) : KP ctx lo s0 s' v := by
  obtain ⟨⟨ms0, h0⟩, hnv, hlo, -⟩ := hI
  obtain ⟨_, _, _, hK⟩ := killed_step h0 hr
  refine ⟨hv.1, fun n c hn => vOk_mono (hv.2.1 n c hn) (by omega) hr.1 hK, hv.2.2⟩

/-! ## Constants and data -/

/-- A value without registers and killing data. -/
theorem kp_clean {ctx : Ctx} {lo : Nat} {s0 s : LState} {v : V} (hk : v.kIn = false)
    (hr : v.regsK = []) (hd : v.regsD = []) : KP ctx lo s0 s v := by
  refine ⟨hk, fun n c h => ?_, fun _ n c h => ?_⟩
  · rw [hr] at h; cases h
  · rw [hd] at h; cases h

theorem kp_int {ctx : Ctx} {lo : Nat} {s0 s : LState} (ty : TypeId) (i : Int) :
    KP ctx lo s0 s ((sem ctx).int ty i) :=
  kp_clean rfl rfl rfl

theorem kp_bool {ctx : Ctx} {lo : Nat} {s0 s : LState} (b : Bool) :
    KP ctx lo s0 s ((sem ctx).bool b) :=
  kp_clean rfl rfl rfl

theorem kp_prim {ctx : Ctx} {lo : Nat} {s0 s : LState} {ty : TypeId} {n : String} {v : V}
    (h : (sem ctx).prim ty n = some v) : KP ctx lo s0 s v := by
  simp only [sem] at h
  split at h
  · obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact kp_clean rfl rfl rfl
  · cases h

/-- Data built from `KP` fields, other than `MInst` data with killed defs. -/
theorem kp_mkData {ctx : Ctx} {lo : Nat} {s0 s : LState} {ty : TypeId} {k : Nat} {fs : List V}
    (hf : ∀ f ∈ fs, KP ctx lo s0 s f) (hk : ¬(ty = tyMInst ∧ isKVariant k = true)) :
    KP ctx lo s0 s ((sem ctx).mkData ty k fs) := by
  show KP ctx lo s0 s (.data ty k fs)
  refine ⟨?_, fun n c hn => ?_, fun ht n c hn => ?_⟩
  · simp only [V.kIn, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
    refine ⟨?_, kInL_eq_false.mpr fun w hw => (hf w hw).1⟩
    by_cases h : ty = tyMInst
    · exact .inr (by simpa using fun h' => hk ⟨h, h'⟩)
    · exact .inl (by simpa using h)
  · obtain ⟨w, hw, hn⟩ := mem_regsKL.mp (by simpa [V.regsK] using hn)
    exact (hf w hw).2.1 n c hn
  · obtain ⟨w, hw, hn⟩ := mem_regsDL.mp (by simpa [V.regsD] using hn)
    exact (hf w hw).2.2 ht n c hn

/-- The fields of a `KP` value are `KP`. -/
theorem kp_unData {ctx : Ctx} {lo : Nat} {s0 s : LState} {ty : TypeId} {v : V} {k : Nat}
    {fs : List V} (hv : KP ctx lo s0 s v) (h : (sem ctx).unData ty v = some (k, fs)) :
    ∀ f ∈ fs, KP ctx lo s0 s f := by
  simp only [sem] at h
  split at h
  · rename_i t k' fs'
    split at h
    · cases h
      intro f hf
      obtain ⟨hk, hr, hd⟩ := hv
      refine ⟨?_, fun n c hn => hr n c ?_, fun ht n c hn => hd ht n c ?_⟩
      · simp only [V.kIn, Bool.or_eq_false_iff] at hk
        exact kInL_eq_false.mp hk.2 f hf
      · simpa [V.regsK] using mem_regsKL.mpr ⟨f, hf, hn⟩
      · simpa [V.regsD] using mem_regsDL.mpr ⟨f, hf, hn⟩
    · cases h
  · cases h

/-! ## Context facts -/

/-- The registers of the CLIF values are vregs of CLIF values (`CtxInv.valueReg`, and
`valReg` is as long as `valDef`). -/
def ValRegK (ctx : Ctx) : Prop :=
  ∀ x r, ctx.valueReg? x = some r → ∀ n c, r = .vreg n c → n < ctx.valDef.size

/-- The instruction data holds no register and no `MInst` data with killed defs. -/
def DataK (ctx : Ctx) : Prop :=
  ∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → info.data.kIn = false ∧
    info.data.regsIn = []

/-- The extern constructors `kp_ctor` does not cover: `invalid_reg` (`Reg.invalid` is a vreg of no
run; only the `nop` and `i128` rules apply it). -/
def Excl : List TermId := [TId.invalid_reg]

/-! ## The registers of the operands -/

theorem regsK_sub : ∀ (v : V), ∀ r ∈ v.regsK, r ∈ v.regsIn
  | .reg _, _, h => h
  | .regs _, _, h => h
  | .regsVec _, _, h => h
  | .op o, r, h => by
    cases o
    case callInfo c =>
      simp only [V.regsK, V.regsIn, opRegsK, opRegs] at h ⊢
      exact List.mem_append.mpr (.inl h)
    all_goals simp_all [V.regsK, V.regsIn, opRegsK, opRegs]
  | .data _ _ fs, r, h => by
    simp only [V.regsK, V.regsIn] at h ⊢
    obtain ⟨w, hw, hr⟩ := mem_regsKL.mp h
    exact regsIn_sub_of_mem hw r (regsK_sub w r hr)
  | .int _, _, h | .bool _, _, h | .ty _, _, h | .inst _, _, h | .value _, _, h | .label _, _, h
  | .labels _, _, h | .values _, _, h | .blockCalls _, _, h => by simp [V.regsK] at h

theorem regsD_sub : ∀ (v : V), ∀ r ∈ v.regsD, r ∈ v.regsIn
  | .op o, r, h => by
    cases o
    case callInfo c =>
      simp only [V.regsD, V.regsIn, opRegsD, opRegs] at h ⊢
      exact List.mem_append.mpr (.inr h)
    all_goals simp_all [V.regsD, V.regsIn, opRegsD, opRegs]
  | .data _ _ fs, r, h => by
    simp only [V.regsD, V.regsIn] at h ⊢
    obtain ⟨w, hw, hr⟩ := mem_regsDL.mp h
    exact regsIn_sub_of_mem hw r (regsD_sub w r hr)
  | .int _, _, h | .bool _, _, h | .ty _, _, h | .inst _, _, h | .value _, _, h | .label _, _, h
  | .labels _, _, h | .values _, _, h | .blockCalls _, _, h | .reg _, _, h | .regs _, _, h
  | .regsVec _, _, h => by simp [V.regsD] at h

/-- A value without registers and killing data. -/
theorem kp_of_regsIn {ctx : Ctx} {lo : Nat} {s0 s : LState} {v : V} (hk : v.kIn = false)
    (hr : v.regsIn = []) : KP ctx lo s0 s v := by
  refine kp_clean hk ?_ ?_
  · cases h : v.regsK with
    | nil => rfl
    | cons r rs =>
      have := regsK_sub v r (by rw [h]; exact List.mem_cons_self)
      rw [hr] at this; cases this
  · cases h : v.regsD with
    | nil => rfl
    | cons r rs =>
      have := regsD_sub v r (by rw [h]; exact List.mem_cons_self)
      rw [hr] at this; cases this

/-- The use vregs of an instruction are its use registers. -/
theorem useVregs_mem {m : MInst} {u : Nat} (h : u ∈ useVregs m) : ∃ c, Reg.vreg u c ∈ useRegsK m := by
  unfold useVregs at h
  cases hops : m.operands with
  | error e => rw [hops] at h; cases h
  | ok ops =>
    rw [hops] at h
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at h
    obtain ⟨o, ⟨ho, hk⟩, rfl⟩ := h
    exact ⟨o.cls, (operands_kinds hops o ho).1 hk⟩

/-! ## The kill contract of an extern constructor -/

/-- An instruction an extern constructor emits (counter from `lo` to `hi`): no `tryCall`, it
kills nothing if the arguments hold no killing data, its uses are registers of the arguments or
fresh vregs, a call's defs are call defs of the arguments. -/
def InstK (args : List V) (lo hi : Nat) (m : MInst) : Prop :=
  (∀ c ti, m ≠ .tryCall c ti) ∧ (kInL args = false → unstored m = []) ∧
    (∀ u ∈ useVregs m, (∃ c, Reg.vreg u c ∈ regsKL args) ∨ (lo ≤ u ∧ u < hi)) ∧
    (∀ c, m = .call c → ∀ q ∈ c.defs, q.2 ∈ regsDL args)

/-- **The kill contract** of one extern constructor call `id args` from `st` returning `v` in
`st'`. -/
structure CtorK (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  vreg : st.nextVreg ≤ st'.nextVreg
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, InstK args st.nextVreg st'.nextVreg m
  kin : kInL args = false → v.kIn = false
  regs : ∀ n c, Reg.vreg n c ∈ v.regsK → Reg.vreg n c ∈ regsKL args ∨
    (st.nextVreg ≤ n ∧ n < st'.nextVreg) ∨ (∃ x, ctx.valueReg? x = some (.vreg n c)) ∨
    id = TId.invalid_reg
  dregs : ∀ n c, Reg.vreg n c ∈ v.regsD → Reg.vreg n c ∈ regsDL args ∨
    Reg.vreg n c ∈ ctx.tryRegs.1 ∨ Reg.vreg n c ∈ ctx.tryRegs.2 ∨ id = TId.gen_call_rets

/-- **The invariants after a constructor call** meeting its kill contract. -/
theorem kp_of_ctorK {ctx : Ctx} {lo : Nat} {s0 s s' : LState} {v : V} {id : TermId}
    {args : List V} (hvr : ValRegK ctx) (hargs : ∀ w ∈ args, KP ctx lo s0 s w)
    (hI : IsK ctx lo s0 s) (hc : CtorK ctx id args s v s') (hid : id ≠ TId.invalid_reg)
    (hgr : id = TId.gen_call_rets → ctx.tryRegs = ([], [])) :
    KP ctx lo s0 s' v ∧ IsK ctx lo s0 s' ∧ RsK s s' := by
  obtain ⟨⟨ms0, h0⟩, hnv, hlo, hold⟩ := hI
  obtain ⟨ms, he, hms⟩ := hc.emit
  have hkin : kInL args = false := kInL_eq_false.mpr fun w hw => (hargs w hw).1
  have hkill : killedL ms = [] := killedL_nil_of fun m hm => (hms m hm).2.1 hkin
  have e' : s'.emitted = s0.emitted ++ (ms0 ++ ms).toArray := by simp [he, h0]
  have hK : killedL (emittedSince s0 s') = killedL (emittedSince s0 s) := by
    rw [emittedSince_eq e', emittedSince_eq h0, killedL_append, hkill, List.append_nil]
  have hKlo : ∀ k ∈ killedL (emittedSince s0 s), lo ≤ k ∧ k < s.nextVreg := by
    intro k hk
    simp only [killedL, List.mem_flatMap] at hk
    obtain ⟨m, hm, hk⟩ := hk
    exact (hold m hm).2.1 k hk
  have hrs : RsK s s' := ⟨hc.vreg, ms, he, by simp [hkill]⟩
  have hargOk : ∀ n c, Reg.vreg n c ∈ regsKL args →
      VOk ctx.valDef.size lo s'.nextVreg (killedL (emittedSince s0 s')) n := by
    intro n c hn
    obtain ⟨w, hw, hn⟩ := mem_regsKL.mp hn
    rw [hK]
    exact vOk_mono ((hargs w hw).2.1 n c hn) (by omega) hc.vreg (fun k hk => .inl hk)
  have hfresh : ∀ n, s.nextVreg ≤ n → n < s'.nextVreg →
      VOk ctx.valDef.size lo s'.nextVreg (killedL (emittedSince s0 s')) n := by
    intro n h1 h2
    rw [hK]
    refine ⟨.inr ⟨by omega, h2⟩, fun hn => ?_⟩
    have := hKlo n hn
    omega
  have hdArg : ctx.tryRegs ≠ ([], []) → ∀ n c, Reg.vreg n c ∈ regsDL args →
      Reg.vreg n c ∈ ctx.tryRegs.1 ∨ Reg.vreg n c ∈ ctx.tryRegs.2 := by
    intro ht n c hn
    obtain ⟨w, hw, hn⟩ := mem_regsDL.mp hn
    exact (hargs w hw).2.2 ht n c hn
  refine ⟨⟨hc.kin hkin, ?_, ?_⟩, ⟨⟨ms0 ++ ms, e'⟩, hnv, by have := hc.vreg; omega, ?_⟩, hrs⟩
  · intro n c hn
    rcases hc.regs n c hn with h | ⟨h1, h2⟩ | ⟨x, hx⟩ | h
    · exact hargOk n c h
    · exact hfresh n h1 h2
    · have hn' := hvr x _ hx n c rfl
      rw [hK]
      refine ⟨.inl hn', fun hk => ?_⟩
      have := hKlo n hk
      omega
    · exact absurd h hid
  · intro ht n c hn
    rcases hc.dregs n c hn with h | h | h | h
    · exact hdArg ht n c h
    · exact .inl h
    · exact .inr h
    · exact absurd (hgr h) ht
  · intro m hm
    rw [emittedSince_eq e'] at hm
    rcases List.mem_append.mp hm with hm | hm
    · rw [← emittedSince_eq h0] at hm
      obtain ⟨h1, h2, h3, h4⟩ := hold m hm
      refine ⟨h1, fun k hk => ?_, fun u hu => ?_, h4⟩
      · have := h2 k hk
        have := hc.vreg
        omega
      · rw [hK]
        exact vOk_mono (h3 u hu) (by omega) hc.vreg (fun k hk => .inl hk)
    · obtain ⟨h1, h2, h3, h4⟩ := hms m hm
      refine ⟨h1, ?_, ?_, ?_⟩
      · intro k hk
        rw [h2 hkin] at hk
        cases hk
      · intro u hu
        rcases h3 u hu with ⟨c, hc'⟩ | ⟨h5, h6⟩
        · exact hargOk u c hc'
        · exact hfresh u h5 h6
      · intro ht c hmc q hq n cl hq2
        have := hdArg ht n cl (hq2 ▸ h4 c hmc q hq)
        rw [hq2]
        exact this

/-! ## The kill contracts of the extern constructors -/

/-- An instruction without killed defs, no call, whose uses are fresh vregs. -/
def FreshInst (lo hi : Nat) (m : MInst) : Prop :=
  NotK m ∧ (∀ c, m ≠ .call c) ∧ ∀ u ∈ useVregs m, lo ≤ u ∧ u < hi

theorem freshInst_of {lo hi : Nat} {m : MInst} (hk : NotK m) (hc : ∀ c, m ≠ .call c)
    (hu : ∀ r ∈ useRegsK m, ∀ n c, r = .vreg n c → lo ≤ n ∧ n < hi) : FreshInst lo hi m := by
  refine ⟨hk, hc, fun u h => ?_⟩
  obtain ⟨c, hc⟩ := useVregs_mem h
  exact hu _ hc u c rfl

theorem freshInst_mono {lo hi hi' : Nat} {m : MInst} (h : FreshInst lo hi m) (hle : hi ≤ hi') :
    FreshInst lo hi' m :=
  ⟨h.1, h.2.1, fun u hu => by have := h.2.2 u hu; omega⟩

theorem instK_of_fresh {args : List V} {lo hi : Nat} {m : MInst} (h : FreshInst lo hi m) :
    InstK args lo hi m := by
  refine ⟨fun c ti he => ?_, fun _ => unstored_nil h.1, fun u hu => .inr (h.2.2 u hu),
    fun c hc => absurd hc (h.2.1 c)⟩
  have := h.1
  rw [he] at this
  exact this

/-- An instruction without killed defs, no call, whose uses are registers of the arguments. -/
theorem instK_of_args {args : List V} {lo hi : Nat} {m : MInst} (hk : NotK m) (hc : ∀ c, m ≠ .call c)
    (hu : ∀ r ∈ useRegsK m, ∀ n c, r = .vreg n c → r ∈ regsKL args) : InstK args lo hi m := by
  refine ⟨fun c ti he => ?_, fun _ => unstored_nil hk, fun u h => ?_, fun c h => absurd h (hc c)⟩
  · rw [he] at hk; exact hk
  · obtain ⟨c, hc⟩ := useVregs_mem h
    exact .inl ⟨c, hu _ hc u c rfl⟩

theorem ctorK_same {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {v : V}
    (hk : kInL args = false → v.kIn = false)
    (hr : ∀ n c, Reg.vreg n c ∈ v.regsK → Reg.vreg n c ∈ regsKL args ∨
      ∃ x, ctx.valueReg? x = some (.vreg n c))
    (hd : ∀ n c, Reg.vreg n c ∈ v.regsD → Reg.vreg n c ∈ regsDL args) :
    CtorK ctx id args st v st :=
  ⟨Nat.le_refl _, ⟨[], by simp, by simp⟩, hk,
    fun n c h => (hr n c h).elim .inl (fun h => .inr (.inr (.inl h))), fun n c h => .inl (hd n c h)⟩

theorem ctorK_invalid {ctx : Ctx} {st : LState} :
    CtorK ctx TId.invalid_reg [] st (.reg Reg.invalid) st :=
  ⟨Nat.le_refl _, ⟨[], by simp, by simp⟩, fun _ => rfl, fun _ _ _ => .inr (.inr (.inr rfl)),
    fun n c h => by simp [V.regsD] at h⟩

theorem ctorK_fresh {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {c : RegClass} :
    CtorK ctx id args st (.reg (st.fresh c).1) (st.fresh c).2 := by
  refine ⟨by simp [LState.fresh], ⟨[], by simp [LState.fresh], by simp⟩, fun _ => rfl,
    fun n c' h => ?_, fun n c h => by simp [V.regsD] at h⟩
  simp only [V.regsK, LState.fresh, List.mem_singleton, Reg.vreg.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact .inr (.inl ⟨Nat.le_refl _, by simp [LState.fresh]⟩)

theorem ctorK_emit {ctx : Ctx} {id : TermId} {i : V} {st : LState} {m : MInst}
    (h : MInst.ofV i = some m) : CtorK ctx id [i] st (.op .unit) (st.emit m) := by
  obtain ⟨h1, h2, h3, h4⟩ := ofV_kill h
  refine ⟨by simp [LState.emit], ⟨[m], by simp [LState.emit], ?_⟩, fun _ => rfl,
    fun n c h => by simp [V.regsK, opRegsK] at h, fun n c h => by simp [V.regsD, opRegsD] at h⟩
  intro m' hm'
  simp only [List.mem_singleton] at hm'
  subst hm'
  refine ⟨h4, fun hk => h2 (by simpa using hk), fun u hu => ?_,
    fun c hc q hq => by simpa using h3 c hc q hq⟩
  unfold useVregs at hu
  cases hops : m'.operands with
  | error e => rw [hops] at hu; cases hu
  | ok ops =>
    rw [hops] at hu
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hu
    obtain ⟨o, ⟨ho, hk⟩, rfl⟩ := hu
    exact .inl ⟨o.cls, by simpa using h1 ops hops o ho hk⟩

/-- The state of `loadConstantFull` (register `rd` and state `s` reached from `st0`). -/
def LCK (st0 : LState) (rd : Reg) (s : LState) : Prop :=
  (∃ n c, rd = .vreg n c ∧ st0.nextVreg ≤ n ∧ n < s.nextVreg) ∧ st0.nextVreg ≤ s.nextVreg ∧
    ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, FreshInst st0.nextVreg s.nextVreg m

theorem lck_step {st0 s : LState} {m : MInst} (hm : FreshInst st0.nextVreg (s.nextVreg + 1) m)
    (hle : st0.nextVreg ≤ s.nextVreg)
    (hem : ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, FreshInst st0.nextVreg s.nextVreg m) :
    LCK st0 (s.fresh .int).1 ((s.fresh .int).2.emit m) := by
  obtain ⟨ms, h5, h6⟩ := hem
  refine ⟨⟨s.nextVreg, .int, rfl, hle, by simp [LState.fresh, LState.emit]⟩,
    by simp [LState.fresh, LState.emit]; omega, ⟨ms ++ [m], by simp [LState.fresh, LState.emit, h5], ?_⟩⟩
  intro m' hm'
  simp only [LState.emit, LState.fresh]
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact freshInst_mono (h6 m' hm') (by omega)
  · simp only [List.mem_singleton] at hm'
    subst hm'
    exact hm

theorem loadConstantFull_k (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) :
    LCK st (loadConstantFull bits se sz value st).1 (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => LCK st x.1 x.2.1) _ _ _ ?_ ?_
  · exact lck_step (freshInst_of trivial (fun c h => by cases h)
      (by simp [useRegsK, MInst.uses, pairUses])) (Nat.le_refl _) ⟨[], by simp, by simp⟩
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => LCK st x.1 x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => LCK st x.1 x.2.1) (fun _ => ?_) fun _ => hx
    obtain ⟨⟨n, c, hrd, h1, h2⟩, h3, ms, h5, h6⟩ := hx
    refine lck_step (s := x.2.1) (freshInst_of trivial (fun c h => by cases h) ?_) h3 ⟨ms, h5, h6⟩
    intro r hr n' c' hr'
    simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_singleton] at hr
    rw [hr, hrd] at hr'
    cases hr'
    omega

theorem ctorK_lc {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {r : Reg} {st' : LState}
    (h : LCK st r st') : CtorK ctx id args st (.reg r) st' := by
  obtain ⟨⟨n, c, rfl, h1, h2⟩, h3, ms, h5, h6⟩ := h
  refine ⟨h3, ⟨ms, h5, fun m hm => instK_of_fresh (h6 m hm)⟩, fun _ => rfl, fun n' c' h => ?_,
    fun n c h => by simp [V.regsD] at h⟩
  simp only [V.regsK, List.mem_singleton, Reg.vreg.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact .inr (.inl ⟨h1, h2⟩)

/-- `gen_call_output`: fresh registers. -/
theorem ctorK_callOutput {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {β : Type}
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, F a b = (a.1.push [(a.2.fresh .int).1], (a.2.fresh .int).2)) :
    CtorK ctx id args st (.regsVec (l.foldl F (#[], st)).1.toList) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (List Reg) × LState =>
      (∀ rs ∈ a.1.toList, ∀ r ∈ rs, ∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < a.2.nextVreg) ∧
      st.nextVreg ≤ a.2.nextVreg ∧ a.2.emitted = st.emitted)
    F l (#[], st) (by simp) (by
      intro b _ a ⟨h1, h2, h4⟩
      rw [hF]
      refine ⟨?_, by simp [LState.fresh]; omega, by simp [LState.fresh, h4]⟩
      intro rs hrs r hr
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrs
      rcases hrs with hrs | rfl
      · obtain ⟨n, c, h, h5, h6⟩ := h1 rs hrs r hr
        exact ⟨n, c, h, h5, by simp [LState.fresh]; omega⟩
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨a.2.nextVreg, .int, rfl, h2, by simp [LState.fresh]⟩)
  obtain ⟨h1, h2, h4⟩ := this
  refine ⟨h2, ⟨[], by simp [h4], by simp⟩, fun _ => rfl, fun n c hn => ?_,
    fun n c h => by simp [V.regsD] at h⟩
  simp only [V.regsK, List.mem_flatten] at hn
  obtain ⟨rs, hrs, hr⟩ := hn
  obtain ⟨n', c', he, h5, h6⟩ := h1 rs hrs _ hr
  cases he
  exact .inr (.inl ⟨h5, h6⟩)

/-- `gen_call_args`: register uses from the arguments, stores of the stack arguments. -/
theorem ctorK_callArgs {ctx : Ctx} {id : TermId} {args : List V} {st : LState}
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags)))
    (hl : ∀ b ∈ l, (∀ p, b.1.1 = .reg p → ∀ n c, p ≠ .vreg n c) ∧ b.1.2 ∈ regsKL args) :
    CtorK ctx id args st (.op (.callArgs (l.foldl F (#[], st)).1.toList)) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (Reg × Reg) × LState =>
      (∀ q ∈ a.1.toList, q.1 ∈ regsKL args ∧ ∀ n c, q.2 ≠ .vreg n c) ∧
      a.2.nextVreg = st.nextVreg ∧
      ∃ ms : List MInst, a.2.emitted = st.emitted ++ ms.toArray ∧
        ∀ m ∈ ms, InstK args st.nextVreg st.nextVreg m)
    F l (#[], st) ⟨by simp, rfl, [], by simp, by simp⟩ (by
      intro b hb a ⟨h1, h2, ms, h4, h5⟩
      rw [hF]
      obtain ⟨hp, hr⟩ := hl b hb
      split
      · rename_i p hbp
        refine ⟨?_, h2, ms, h4, h5⟩
        intro q hq
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact h1 q hq
        · exact ⟨hr, hp p hbp⟩
      · rename_i off _
        refine ⟨h1, by simp [LState.emit, h2],
          ms ++ [MInst.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags],
          by simp [LState.emit, h4], ?_⟩
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h5 m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          refine instK_of_args trivial (fun c h => by cases h) ?_
          intro r hr' n c _
          simp only [useRegsK, MInst.uses, AMode.regs, pairUses, List.append_nil,
            List.mem_singleton] at hr'
          rw [hr']
          exact hr)
  obtain ⟨h1, h2, ms, h4, h5⟩ := this
  refine ⟨by omega, ⟨ms, h4, fun m hm => by rw [h2]; exact h5 m hm⟩, fun _ => rfl, fun n c hn => ?_,
    fun n c h => by simp [V.regsD, opRegsD] at h⟩
  simp only [V.regsK, opRegsK, pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
    or_false] at hn
  obtain ⟨q, hq, hr⟩ := hn
  obtain ⟨hq1, hq2⟩ := h1 q hq
  rcases hr with hr | hr
  · exact .inl (hr ▸ hq1)
  · exact absurd hr.symm (hq2 n c)

/-- `gen_return`: `Rets` of argument registers. -/
theorem ctorK_rets {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {l : List (Reg × Reg)}
    (h : ∀ q ∈ l, q.1 ∈ regsKL args) : CtorK ctx id args st (.op .unit) (st.emit (.rets l)) := by
  refine ⟨by simp [LState.emit], ⟨[.rets l], by simp [LState.emit], ?_⟩, fun _ => rfl,
    fun n c h => by simp [V.regsK, opRegsK] at h, fun n c h => by simp [V.regsD, opRegsD] at h⟩
  intro m hm
  simp only [List.mem_singleton] at hm
  subst hm
  refine instK_of_args trivial (fun c h => by cases h) ?_
  intro r hr n c _
  simp only [useRegsK, MInst.uses, pairUses, List.nil_append, List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  exact h q hq

/-- `gen_call_info`/`gen_call_ind_info`: the call's registers come from the arguments. -/
theorem ctorK_callInfo {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {c : CallInfo}
    {k : Nat} (hr : ∀ r ∈ opRegsK (.callInfo c), r ∈ regsKL args)
    (hd : ∀ r ∈ opRegsD (.callInfo c), r ∈ regsDL args) :
    CtorK ctx id args st (.op (.callInfo c)) { st with outgoing := max st.outgoing k } :=
  ⟨Nat.le_refl _, ⟨[], by simp, by simp⟩, fun _ => rfl, fun n c h => .inl (hr _ h),
    fun n c h => .inl (hd _ h)⟩

/-- `gen_try_call_rets`: the `try_call`'s registers in call defs, physical registers. -/
theorem ctorK_tryRets {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {k : Nat}
    {ps : List Reg} (hps : retRegs k = some ps) (cc : Option Clif.CallConv)
    (f : Reg × Reg → Bool) :
    CtorK ctx id args st
      (.op (.callRets (ps.zip ctx.tryRegs.1 ++ List.filter f ((payloadRegs cc).zip ctx.tryRegs.2))))
      st := by
  refine ⟨Nat.le_refl _, ⟨[], by simp, by simp⟩, fun _ => rfl,
    fun n c h => by simp [V.regsK, opRegsK] at h, fun n c hr => ?_⟩
  simp only [V.regsD, opRegsD, pairRegs, List.mem_flatMap, List.mem_append, List.mem_filter,
    List.mem_cons, List.mem_nil_iff, or_false] at hr
  obtain ⟨⟨a, b⟩, hq, hr⟩ := hr
  rcases hq with hq | ⟨hq, -⟩
  · have hz := List.of_mem_zip hq
    rcases hr with hr | hr
    · exact absurd hr.symm (retRegs_phys hps _ hz.1 n c)
    · exact .inr (.inl (hr ▸ hz.2))
  · have hz := List.of_mem_zip hq
    rcases hr with hr | hr
    · exact absurd hr.symm (payloadRegs_phys cc _ hz.1 n c)
    · exact .inr (.inr (.inl (hr ▸ hz.2)))

/-- `CtorK` of every successful result of a constructor call. -/
def CtorKP (ctx : Ctx) (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) :
    Prop :=
  ∀ v st', r = .ok (v, st') → CtorK ctx id args st v st'

/-- Close `CtorK` of a constructor that keeps the state. -/
macro "ctork_same" : tactic => `(tactic| (refine ctorK_same ?_ ?_ ?_ <;> simp_all (config := { decide := true }) [V.regsK, V.regsD, V.kIn, opRegsK, opRegsD, pairRegs, isKVariant] <;> done))

set_option maxHeartbeats 4000000 in
/-- **Every extern constructor** meets its kill contract. -/
theorem externCtor_k (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorKP ctx st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      exact ctorK_same (fun _ => rfl) (by simp [V.regsK]) (by simp [V.regsD])
    · cases h
  · apply externCtor_split _ (CtorKP ctx st)
    all_goals
      intros
      unfold CtorKP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | ctork_same
      | (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq; ctork_same)
      | exact ctorK_invalid
      | exact ctorK_fresh
      | exact ctorK_emit ‹_›
      | exact ctorK_lc (loadConstantFull_k _ _ _ _ _)
      | exact ctorK_callOutput _ _ (fun _ _ => rfl)
      | exact ctorK_tryRets ‹_› _ _
      | (refine ctorK_same (fun _ => rfl) ?_ (by simp [V.regsD])
         intro n c hn
         simp only [V.regsK, List.mem_singleton] at hn
         subst hn
         first
         | exact .inr ⟨_, ‹_›⟩
         | exact .inl (by simpa [V.regsK] using List.mem_of_getElem? ‹_›))
      | (refine ctorK_same (fun _ => rfl) ?_ (by simp [V.regsD])
         intro n c hn
         simp only [V.regsK, List.mem_flatten, List.mem_map] at hn
         obtain ⟨_, ⟨r', hr', rfl⟩, hr⟩ := hn
         simp only [List.mem_singleton] at hr
         subst hr
         obtain ⟨x, -, he⟩ := mapM_mem ‹_› _ hr'
         exact .inr ⟨x, he⟩)
      | (refine ctorK_rets ?_
         intro q hq
         obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ (List.of_mem_zip hq).1
         simp only [regsKL_cons, regsKL_nil, V.regsK, List.append_nil, List.mem_flatten]
         exact ⟨l, hl, hrl⟩)
      | (refine ctorK_callArgs _ _ (fun _ _ => rfl) ?_
         intro b hb
         have hz := List.of_mem_zip hb
         have hz1 := List.of_mem_zip hz.1
         refine ⟨fun p hp => sigArgLocs_phys ‹_› _ (hp ▸ hz1.1) p rfl, ?_⟩
         obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz1.2
         simp only [regsKL_cons, regsKL_nil, V.regsK, opRegsK, List.append_nil, List.nil_append,
           List.mem_flatten]
         exact ⟨l, hl, hrl⟩)
      | exact ⟨Nat.le_refl _, ⟨[], by simp, by simp⟩, fun _ => rfl,
          fun n c h => by simp [V.regsK, opRegsK] at h, fun n c _ => .inr (.inr (.inr rfl))⟩
      | (refine ctorK_callInfo ?_ ?_ <;> intro r hr <;>
          simp_all [opRegsK, opRegsD, V.regsK, V.regsD] <;> (rcases hr with h | h <;> simp [h]))

/-- **Extern constructors keep the invariants** (all but `invalid_reg`; `gen_call_rets` only
outside a `try_call`'s lowering). -/
theorem kp_ctor {ctx : Ctx} {lo : Nat} {s0 s s' : LState} {term : Term} {vs : List V} {v : V}
    (hvr : ValRegK ctx) (hargs : ∀ w ∈ vs, KP ctx lo s0 s w) (hI : IsK ctx lo s0 s)
    (h : (sem ctx).ctor term vs s = .ok (v, s')) (hex : term.id ∉ Excl)
    (hgr : term.id = TId.gen_call_rets → ctx.tryRegs = ([], [])) :
    KP ctx lo s0 s' v ∧ IsK ctx lo s0 s' ∧ RsK s s' :=
  kp_of_ctorK hvr hargs hI (externCtor_k ctx term vs s v s' h)
    (fun he => hex (by simp [Excl, he])) hgr

/-! ## Extern extractors -/

/-- The outputs of an extractor hold no register and no killing data. -/
def ExtKP (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → ∀ f ∈ fs, f.kIn = false ∧ f.regsIn = []

set_option maxHeartbeats 2000000 in
theorem externExtract_k {ctx : Ctx} (hd : DataK ctx) (t : Term) (v : V) (st : LState) :
    ExtKP (externExtract ctx t v st) := by
  unfold externExtract
  split
  · intro fs h
    split at h
    · cases h
      simp [V.kIn, V.regsIn]
    · cases h
  · intro fs h; cases h
  · apply externExtract_split _ (fun _ _ r => ExtKP r)
    all_goals
      intros
      unfold ExtKP
      intro fs h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (simp (config := { decide := true }) [V.kIn, V.regsIn, opRegs]; done)
      | (simp only [List.forall_mem_cons]
         exact ⟨⟨rfl, rfl⟩, hd _ _ ‹_›, fun _ h => by cases h⟩)

/-- **Extern extractors give `KP` values.** -/
theorem kp_extract {ctx : Ctx} {lo : Nat} {s0 s : LState} (hd : DataK ctx) {term : Term} {v : V}
    {st : LState} {fs : List V} (h : (sem ctx).extract term v st = .ok fs) :
    ∀ f ∈ fs, KP ctx lo s0 s f := fun f hf =>
  have := externExtract_k hd term v st fs h f hf
  kp_of_regsIn this.1 this.2

/-! ## The context facts of the driver's contexts -/

theorem valRegK_mk {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    (hs : ctx.valReg.size = ctx.valDef.size) : ValRegK ctx := by
  intro x r hx n c hr
  have hlt : x < ctx.valReg.size := by
    simp only [Ctx.valueReg?] at hx
    cases h : ctx.valReg[x]? with
    | none => rw [h] at hx; cases hx
    | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
  rw [hreg x r hx] at hr
  cases hr
  omega

/-- `ValRegK` from `CtxInv` (value `x` has vreg `x`) and the length of `valReg`. -/
theorem valRegK_of {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hs : ctx.valReg.size = ctx.valDef.size) : ValRegK ctx :=
  valRegK_mk hctx.valueReg hs

/-- **`buildCtx`'s context** meets `ValRegK`. -/
theorem valRegK_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : ValRegK ctx :=
  valRegK_mk (ctxSpec_of hb).regEq (ctxFacts_of hb).size.2.1

theorem valRegK_termCtx {ctx : Ctx} (h : ValRegK ctx) (ti : Nat) (data : V) :
    ValRegK (termCtx ctx ti data) := h

theorem valRegK_tryCtx {ctx : Ctx} (h : ValRegK ctx) (ti : Nat) (data : V)
    (trs : List Reg × List Reg) : ValRegK (tryCtx ctx ti data trs) := h

theorem kIn_mkVariant {ty : TypeId} {name : String} {fs : List V} (hty : ty ≠ tyMInst)
    (h : kInL fs = false) : (mkVariant ty name fs).kIn = false := by
  unfold mkVariant
  split
  · simp [V.kIn, hty, h]
  · rfl

theorem kInL_nil' : kInL [] = false := rfl

theorem kInL_cons' {v : V} {vs : List V} (h1 : v.kIn = false) (h2 : kInL vs = false) :
    kInL (v :: vs) = false := by simp [h1, h2]

theorem kIn_int {i : Int} : (V.int i).kIn = false := rfl
theorem kIn_value {x : Nat} : (V.value x).kIn = false := rfl
theorem kIn_values {xs : List Nat} : (V.values xs).kIn = false := rfl
theorem kIn_op {o : Opnd} : (V.op o).kIn = false := rfl
theorem kIn_blockCalls {bs : List Nat} : (V.blockCalls bs).kIn = false := rfl

/-- Build `kIn = false` of an `instDataV` term. -/
macro "k_data" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply kIn_mkVariant (by decide)
    | with_reducible exact kInL_nil'
    | with_reducible apply kInL_cons'
    | with_reducible exact kIn_int
    | with_reducible exact kIn_value
    | with_reducible exact kIn_values
    | with_reducible exact kIn_op
    | with_reducible exact kIn_blockCalls))

set_option maxRecDepth 20000 in
/-- The data of a statement holds no `MInst` data. -/
theorem instData_kIn {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    d.kIn = false := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       k_data)

/-- **The data of a terminator** holds no register and no `MInst` data. -/
theorem termData_kClean {t : Clif.Terminator} {d : V} (h : termData t = .ok d) :
    d.kIn = false ∧ d.regsIn = [] := by
  refine ⟨?_, (termData_ok h).1⟩
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       k_data)

set_option maxRecDepth 20000 in
/-- **The data of a `try_call`** holds no register and no `MInst` data. -/
theorem tryCallData_kClean {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : d.kIn = false ∧ d.regsIn = [] := by
  refine ⟨?_, (tryCallData_ok h).1⟩
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           k_data)

/-- **`buildCtx`'s context** meets `DataK`: its entries are the terminators' placeholders and
the statements' `instData`. -/
theorem dataK_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : DataK ctx := by
  have sp := ctxSpec_of hb
  intro i info hi
  rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨d, hd⟩ := ((sp.blockC B hB).2 s hs).1
    have hdo : (infoOf f s).data = d := by
      show dataOf f s = d
      unfold dataOf
      rw [hd]
    rw [hdo]
    exact ⟨instData_kIn hd, (instData_ok hd).1⟩

/-- Setting a terminator slot to clean data keeps `DataK`. -/
theorem dataK_termCtx {ctx : Ctx} (h : DataK ctx) {data : V} (hd : data.kIn = false ∧ data.regsIn = [])
    (ti : Nat) : DataK (termCtx ctx ti data) := by
  intro j info hj
  by_cases hji : j = ti
  · subst hji
    by_cases hlt : j < ctx.insts.size
    · have : (termCtx ctx j data).insts[j]? = some ⟨data, [], [], none⟩ := by
        show (ctx.insts.set! j _)[j]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [this] at hj
      cases hj
      exact hd
    · have : (termCtx ctx j data).insts = ctx.insts := by
        show ctx.insts.set! j _ = _
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [this] at hj
      exact h j info hj
  · rw [termCtx_insts_ne hji] at hj
    exact h j info hj

theorem dataK_tryCtx {ctx : Ctx} (h : DataK ctx) {data : V} (hd : data.kIn = false ∧ data.regsIn = [])
    (ti : Nat) (trs : List Reg × List Reg) : DataK (tryCtx ctx ti data trs) :=
  dataK_termCtx h hd ti

end Backend.Proof.Kill
