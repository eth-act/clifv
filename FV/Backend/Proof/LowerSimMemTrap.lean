import FV.Backend.Proof.IselMemTrap
import FV.Backend.Proof.LowerSim

/-!
# The driver simulation of a memory trap (A3, #412, slice F3)

`docs/plans/memfault.md`, "Backend layers". `driver_correct` realises the explicit traps of a CLIF
run (`RunPrem.stmt`: only `div` traps) by a VCode instruction that halts with the code
(`VTrapFrom`). A memory trap of an `atomic_rmw`/`atomic_cas` (`Clif.memTrapInst`) is realised
by the VCode run reaching the statement's LL/SC loop (`AtomicLowered`), whose trap code is the
CLIF flags' and whose address use holds the CLIF address (`VMemTrapFrom`): the VCode semantics
is unchanged (the loop's access is the Arm machine's, which faults or not by the memory map).

* `VMemTrapFrom vc sem vs c A`: the VCode run from `vs` reaches a loop with trap code `c`,
  access size `n` and address use `u` with `A (lo64 u) n`;
* `stmt_memtrap`: at a matching state whose statement traps at memory, `VMemTrapFrom` with the
  CLIF access's address and size;
* `RunPremM`: `RunPrem` whose statement clause also allows `memTrapInst` traps;
* `reach_match`: every state the CLIF run reaches by continuing steps (`Reach`) is matched by a
  state of the VCode run, up to the two-step `try_call` (`MatchT`);
* **`driver_memtrap`**: a trap of the CLIF run from the entry is an explicit trap of the VCode
  run (`VTrapFrom`) or a memory trap (`VMemTrapFrom`) whose address and size satisfy every
  property `Q` of the run's memory traps (`Clif.MemTrapAt`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **From `vs`, the VCode run reaches an LL/SC loop** with trap code `c` and access size `n`,
whose address use value `u` satisfies `A (lo64 u) n`. -/
def VMemTrapFrom {W : Type} (vc : VCode) (sem : ISem CV W) (vs : VState CV W) (c : Clif.TrapCode)
    (A : BitVec 64 → Nat → Prop) : Prop :=
  ∃ b k ρ w vb i ops u us n, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    vuses ops ρ = u :: us ∧ loopTrap? i = some (c, n) ∧ A (lo64 u) n

theorem VMemTrapFrom.prefix {W : Type} {vc : VCode} {sem : ISem CV W} {vs vs' : VState CV W}
    {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VMemTrapFrom vc sem vs' c A) :
    VMemTrapFrom vc sem vs c A := by
  obtain ⟨b, k, ρ, w, vb, i, ops, u, us, n, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, i, ops, u, us, n, h.trans hs, h1⟩

/-- The CLIF-level property `Q a n` of an access `[a, a + n)` as a property of the 64-bit
address. -/
def addrPred (Q : Nat → Nat → Prop) : BitVec 64 → Nat → Prop :=
  fun u n => ∃ a, u = BitVec.ofNat 64 a ∧ Q a n

theorem lo64_of_holds_i64 {v : Clif.Val} {x : CV} (h : VHolds v x) (ht : v.ty = .i64) :
    lo64 x = BitVec.ofNat 64 v.toNat := by
  obtain ⟨ty, bits⟩ := v
  simp only at ht
  subst ht
  simp only [VHolds] at h
  apply BitVec.eq_of_toNat_eq
  rw [← h]
  simp [lo64, Clif.Val.toNat, Clif.Ty.width]

theorem ofClif_bytes_eq (t : Clif.Ty) : (CTy.ofClif t).bytes = t.bytes := by
  cases t <;> rfl

theorem ofNat_effAddr0 (v : Clif.Val) :
    BitVec.ofNat 64 (Clif.effAddr v 0) = BitVec.ofNat 64 v.toNat := by
  simp only [Clif.effAddr, Int.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have : ((↑v.toNat : Int) % (2 ^ 64 : Int)).toNat = v.toNat % 2 ^ 64 := by omega
  rw [this, Nat.mod_mod]

theorem ofClif_eq_int64 {t : Clif.Ty} (h : CTy.ofClif t = .int 64) : t = .i64 := by
  cases t <;> simp_all [CTy.ofClif]

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- **A memory trap at a matching state, at the statement's first instruction**: the statement's
lowered loop is the VCode instruction at the matching position `k = pos b j` (the first of its
nonempty segment); its code is the trap's, its address use holds the CLIF address. -/
theorem stmt_memtrap0 (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hmt : Clif.memTrapInst stm.inst = true) {c : Clif.TrapCode}
    (hs : Clif.step env p s = .trapped c) {Q : Nat → Nat → Prop}
    (hQ : ∀ a n, Clif.MemTrapAt env p s c a n → Q a n) :
    ∃ B j, f.blocks[b]? = some B ∧ B.body[j]? = some stm ∧ k = pos f R bl b j ∧
      0 < (seg f R bl b j).length ∧
      ∃ vb i ops u us n, vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧
        i.operands = .ok ops ∧ vuses ops ρ = u :: us ∧ loopTrap? i = some (c, n) ∧
        addrPred Q (lo64 u) n := by
  obtain ⟨-, hfunc, -, -, B, j, hB, -, -, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB
  subst hk
  obtain ⟨hjlt, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨info, hinfo, hclif, -⟩, hemp, -, ⟨tr, hrun⟩, -⟩ := hstmts j stm sl hstm hsl
  obtain ⟨ms, hem, hshape⟩ := atomicLowered_runTerm H.shape.ctxInv H.subE hinfo hclif hmt hrun
  rw [hemp, Array.empty_append] at hem
  have hemL : sl.st'.emitted.toList = ms := by simp [hem]
  obtain ⟨hargs, -, -, -, -⟩ := H.cert.stmt b B L j stm sl hB hL hstm hsl
  obtain ⟨a, n, fl, hmta, -, hfl, hcases⟩ := Clif.memTrapAt_of_trapped hbody hmt hs
  have hQa : Q a n := hQ a n hmta
  obtain ⟨-, -, st', rest', hb', hacc⟩ := hmta
  rw [hbody] at hb'
  obtain ⟨rfl, -⟩ := List.cons.inj hb'
  have hseg := (seg_at hcode htne hjlt).1
  have hlen0 := congrArg List.length (seg_eq (R := R) hB hL hstm hsl)
  rw [seg_eq hB hL hstm hsl, hemL] at hseg
  rw [hemL] at hlen0
  -- the address value: held, of type `i64`
  have haddr : ∀ q, memAddr? stm.inst = some q → q ∈ instArgs stm.inst → ∀ pv,
      s.frame.get q = .ok pv → lo64 (ρ (gn q)) = BitVec.ofNat 64 pv.toNat := by
    intro q hq hqa pv hpv
    have hqA := hargs q hqa
    obtain ⟨v, hv, hh⟩ := hheld q hqA
    have hpv' : s.frame.regs q = some pv := by
      simp only [Clif.Frame.get] at hpv
      cases hr : s.frame.regs q with
      | none => rw [hr] at hpv; cases hpv
      | some v' => rw [hr] at hpv; cases hpv; rfl
    rw [hpv'] at hv; cases hv
    have h64 := H.shape.ctxInv.addr64 _ info stm.inst q hinfo hclif hq
    have hty := hcons.2 q _ pv h64 (by rw [restrict_regs_of_mem hqA]; exact hpv')
    exact lo64_of_holds_i64 hh (ofClif_eq_int64 hty)
  rcases hcases with ⟨op, ty, q, x, hi, rfl⟩ | ⟨ty, q, e, x, hi, rfl⟩
  · obtain ⟨hety, lop, d, d1, d2, rfl⟩ := hshape.1 op ty fl q x hi
    rw [hi] at hacc
    cases hacc with
    | atomicRmw hpv =>
      rename_i pv
      have hk0 := hseg 0 (by simp)
      simp only [List.cons_append, List.map_cons, List.getElem_cons_zero, Nat.add_zero] at hk0
      simp only [MInst.mapRegs, H.shape.ren.vreg] at hk0
      refine ⟨B, j, hB, hstm, rfl, by rw [hlen0]; simp, vb, _, _, ρ (gn q), [ρ (gn x)], ty.bytes,
        hvb, hk0, operands_rmwLoop _ _ _ _ _ _ _ _, by simp [vuses, Operand.isUse], ?_, ?_⟩
      · simp [loopTrap?, hfl, ofClif_bytes_eq, atomTy_ofClif hety]
      · exact ⟨_, by rw [haddr q (by simp [hi, memAddr?]) (by simp [hi, instArgs]) pv hpv,
          ofNat_effAddr0], hQa⟩
  · obtain ⟨hety, d, d1, rfl⟩ := hshape.2 ty fl q e x hi
    rw [hi] at hacc
    cases hacc with
    | atomicCas hpv =>
      rename_i pv
      have hk0 := hseg 0 (by simp)
      simp only [List.cons_append, List.map_cons, List.getElem_cons_zero, Nat.add_zero] at hk0
      simp only [MInst.mapRegs, H.shape.ren.vreg] at hk0
      refine ⟨B, j, hB, hstm, rfl, by rw [hlen0]; simp, vb, _, _, ρ (gn q),
        [ρ (gn e), ρ (gn x)], ty.bytes, hvb, hk0, operands_casLoop _ _ _ _ _ _ _,
        by simp [vuses, Operand.isUse], ?_, ?_⟩
      · simp [loopTrap?, hfl, ofClif_bytes_eq, atomTy_ofClif hety]
      · exact ⟨_, by rw [haddr q (by simp [hi, memAddr?]) (by simp [hi, instArgs]) pv hpv,
          ofNat_effAddr0], hQa⟩

/-- **A memory trap at a matching state**: the statement's lowered loop is the VCode instruction
at the matching position; its code is the trap's, its address use holds the CLIF address. -/
theorem stmt_memtrap (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hmt : Clif.memTrapInst stm.inst = true) {c : Clif.TrapCode}
    (hs : Clif.step env p s = .trapped c) {Q : Nat → Nat → Prop}
    (hQ : ∀ a n, Clif.MemTrapAt env p s c a n → Q a n) :
    VMemTrapFrom vc sem ⟨b, k, ρ, w⟩ c (addrPred Q) := by
  obtain ⟨-, -, -, -, -, -, vb, i, ops, u, us, n, h1, h2, h3, h4, h5, h6⟩ :=
    stmt_memtrap0 H hm hbody hmt hs hQ
  exact ⟨b, k, ρ, w, vb, i, ops, u, us, n, .refl _, h1, h2, h3, h4, h5, h6⟩

/-- **The run premises with memory traps**: `RunPrem` whose statement clause also allows the
memory traps of `Clif.memTrapInst`. -/
structure RunPremM (env : Clif.Env) (p : Clif.Program) (f : Clif.Function) (cs : Clif.State) :
    Prop where
  stmt : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true ∨ Clif.memTrapInst st.inst = true
  tryCall : ∀ s c fn args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCall fn args et → ∀ B ∈ f.blocks,
      B.term ≠ .tryCall fn args et
  tryCallInd : ∀ s c callee args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et → ∀ B ∈ f.blocks,
      B.term ≠ .tryCallIndirect callee args et
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ f.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ f.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- `RunPrem` is the special case without memory traps. -/
theorem RunPrem.toM {cs : Clif.State} (h : RunPrem env p f cs) : RunPremM env p f cs :=
  ⟨fun s c st rest hr hs hb => .inl (h.stmt s c st rest hr hs hb), h.tryCall, h.tryCallInd,
    h.indirect, h.tryIndirect⟩

/-- **A matched state, or the state between the two steps of a `try_call`** (its step
continues to a matched state, never traps). -/
def MatchT (_H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (s : Clif.State)
    (vs : VState CV W) : Prop :=
  Match f ctx R gn bl A MR slots s vs ∨
    ((∀ c, Clif.step env p s ≠ .trapped c) ∧ ∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run vs) (.run vs') ∧ Match f ctx R gn bl A MR slots s' vs')

/-- One continuing step from a matched or intermediate state. -/
theorem matchT_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs s s' : Clif.State}
    (hP : RunPremM env p f cs) (hr : Reach env p cs s) {vs : VState CV W}
    (hm : MatchT (slots := slots) H s vs) (hs : Clif.step env p s = .next s') :
    ∃ vs', Star (VStep vc sem) (.run vs) (.run vs') ∧ MatchT (slots := slots) H s' vs' := by
  rcases hm with hm | ⟨-, hnx⟩
  · obtain ⟨b, k, ρ, w⟩ := vs
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨vs', hstar, hm'⟩ := (term_step H hm hbody hty).1 s' hs
        exact ⟨vs', hstar, .inl hm'⟩
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
          cases ht : s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => hP.tryIndirect s callee args et hr hbody ht
            ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨-, Tnx⟩ := term_step_try H hm hbody hT hind
        obtain ⟨N1, -, N3⟩ := Tnx s' hs
        exact ⟨_, .refl _, .inr ⟨N1, N3⟩⟩
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      obtain ⟨vs', hstar, hm'⟩ := (stmt_step H hm hbody hind).1 s' hs
      exact ⟨vs', hstar, .inl hm'⟩
  · obtain ⟨vs', hstar, hm'⟩ := hnx s' hs
    exact ⟨vs', hstar, .inl hm'⟩

/-- **Every reachable state is matched** (or intermediate) by a state of the VCode run. -/
theorem reach_match (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (hP : RunPremM env p f cs) :
    ∀ {s s' : Clif.State}, Reach env p s s' → Reach env p cs s → ∀ {vs : VState CV W},
      MatchT (slots := slots) H s vs →
      ∃ vs', Star (VStep vc sem) (.run vs) (.run vs') ∧ MatchT (slots := slots) H s' vs' := by
  intro s s' h
  induction h with
  | refl => intro _ vs hm; exact ⟨vs, .refl _, hm⟩
  | step h1 _ ih =>
    intro hr vs hm
    obtain ⟨vs1, hst1, hm1⟩ := matchT_step H hP hr hm h1
    obtain ⟨vs2, hst2, hm2⟩ := ih (hr.snoc h1) hm1
    exact ⟨vs2, hst1.trans hst2, hm2⟩

/-- **The trapping state**: a trap at a matched or intermediate state is an explicit trap or a
memory trap of the VCode run. -/
theorem trap_matchT (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs s : Clif.State}
    (hP : RunPremM env p f cs) (hr : Reach env p cs s) {vs : VState CV W}
    (hm : MatchT (slots := slots) H s vs) {c : Clif.TrapCode}
    (hs : Clif.step env p s = .trapped c) {Q : Nat → Nat → Prop}
    (hQ : ∀ a n, Clif.MemTrapAt env p s c a n → Q a n) :
    VTrapFrom vc sem vs c ∨ VMemTrapFrom vc sem vs c (addrPred Q) := by
  rcases hm with hm | ⟨hnt, -⟩
  · obtain ⟨b, k, ρ, w⟩ := vs
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false => exact .inl ((term_step H hm hbody hty).2.2 c hs)
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        cases ht : s.frame.term with
        | tryCall fn args et =>
          exact absurd (hterm.symm.trans ht) (hP.tryCall s c fn args et hr hs hbody ht B hBmem)
        | tryCallIndirect callee args et =>
          exact absurd (hterm.symm.trans ht)
            (hP.tryCallInd s c callee args et hr hs hbody ht B hBmem)
        | _ => rw [ht] at hty; cases hty
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      rcases hP.stmt s c st rest hr hs hbody with hexp | hmt
      · exact .inl ((stmt_step H hm hbody hind).2 c hs hexp)
      · exact .inr (stmt_memtrap H hm hbody hmt hs hQ)
  · exact absurd hs (hnt c)

/-- A trapping run reaches a state whose step traps. -/
theorem runLoop_trapped_reach {env : Clif.Env} {p : Clif.Program} :
    ∀ (fuel : Nat) (s : Clif.State) (c : Clif.TrapCode), Clif.runLoop env p fuel s = .trapped c →
      ∃ s', Reach env p s s' ∧ Clif.step env p s' = .trapped c
  | 0, _, _, h => by simp at h
  | fuel + 1, s, c, h => by
    rw [Clif.runLoop_succ] at h
    cases hs : Clif.step env p s with
    | next s1 =>
      rw [hs] at h
      obtain ⟨s', hr, h'⟩ := runLoop_trapped_reach fuel s1 c h
      exact ⟨s', .step hs hr, h'⟩
    | trapped c' => rw [hs] at h; cases h; exact ⟨s, .refl _, hs⟩
    | done _ _ => rw [hs] at h; cases h
    | stuck _ => rw [hs] at h; cases h

end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The driver lemma for traps with memory traps (CLIF → VCode).** A trap of the CLIF run of
`f` from an entry state (as `driver_correct`; run premises `RunPremM`) is an explicit trap of the
VCode run from the entry (`VTrapFrom`) or reaches the trapping atomic's LL/SC loop with the same
code (`VMemTrapFrom`), its address and size satisfying every property `Q` of the run's memory
traps. -/
theorem driver_memtrap (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPremM env p f cs) {Q : Nat → Nat → Prop}
    (hQ : ∀ s c a n, Reach env p cs s → Clif.MemTrapAt env p s c a n → Q a n)
    (fuel : Nat) (c : Clif.TrapCode) (hrun : Clif.runLoop env p fuel cs = .trapped c) :
    VTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c ∨ VMemTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c (addrPred Q) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_step H hds hMem hMR hB0 hcall hfunc hslots hbody hterm
    hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  obtain ⟨s, hr, hs⟩ := runLoop_trapped_reach fuel cs c hrun
  obtain ⟨vs, hstar', hm'⟩ := reach_match H hP hr (.refl _) (.inl hm)
  rcases trap_matchT H hP hr hm' hs (hQ s c · · hr) with h | h
  · exact .inl (VTrapFrom.prefix (hstar.trans hstar') h)
  · exact .inr (VMemTrapFrom.prefix (hstar.trans hstar') h)

end

end Backend.Proof.Driver
