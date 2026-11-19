import FV.Opt.Proof.SemSimM

/-!
# Memory-aware simulations: related states and steps where no callee unwinds (#1119)

The states with unwinding (`XState`) are related by `SRMU`: `SRU` (`FV/Opt/Proof/SemSimU.lean`)
with the frame relation taken at the state's memory (`GRMU`), and the suspended callers related
through continuations (`ContM`) and pending tables (`TabRelM`) valid at every memory with the
symbols. The step lemmas are `SemSimU`'s, with the memory threaded: a local step lands both sides
in the source's memory; a callee's return, an extern's return and a handler entry use the
"every memory" side conditions.
-/

namespace Opt

open Clif

/-! ## Related states -/

/-- The memory-aware frame relation with unwinding, at memory `m`: some `IsSimMU` relates the
frames at `m`, or their pending jumps. -/
def GRMU (syms : String → Option Nat) (fr fr' : Frame) (m : Mem) : Prop :=
  ∃ R, IsSimMU syms R ∧ (R fr fr' m ∨ JR (fun x y => R x y m) fr fr')

theorem GRMU.of {syms R} (hR : IsSimMU syms R) {a b : Frame} {m : Mem} (h : R a b m) :
    GRMU syms a b m :=
  ⟨R, hR, .inl h⟩

/-- A returned `try_call`'s caller frames (`jumpFrame`) are related. -/
theorem TContM.toContMU {syms R} (hR : IsSimMU syms R) {fr fr' : Frame} {rs rs' : List ValueId}
    {bc bc' : BlockCall} {rtys : List Ty} (h : TContM syms R fr rs bc fr' rs' bc' rtys) :
    ContM syms (GRMU syms) (jumpFrame fr bc) rs (jumpFrame fr' bc') rs' rtys := by
  intro vs regs m ht hm hs
  obtain ⟨regs', h1, h2⟩ := h vs regs m ht hm hs
  refine ⟨regs', h1, R, hR, .inr ⟨rfl, rfl, bc, bc', rfl, rfl, fun a1 he => ?_⟩⟩
  have he' : enterBlock { fr with regs } bc = .ok a1 := by
    rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he
  obtain ⟨b1, hb1, hr⟩ := h2 a1 he'
  exact ⟨b1, by rw [← hb1, ← enterBlock_bt { fr' with regs := regs' } [] (.jump bc')]; rfl, hr⟩

/-- The pending tables `t`/`t'` of suspended callers `c`/`c'` catch alike, at handler frames
related at every memory with the symbols. -/
def TabRelM (syms : String → Option Nat) (c : Frame) (t : Option ExnTable) (c' : Frame)
    (t' : Option ExnTable) : Prop :=
  ∀ e, (t.bind (catchIn c · e) = none → t'.bind (catchIn c' · e) = none) ∧
    ∀ fr1, t.bind (catchIn c · e) = some (.ok fr1) →
      ∃ fr1', t'.bind (catchIn c' · e) = some (.ok fr1') ∧
        ∀ m, m.symbols = syms → GRMU syms fr1 fr1' m

theorem TabRelM.none' (syms : String → Option Nat) (c c' : Frame) :
    TabRelM syms c none c' none :=
  fun _ => ⟨fun _ => rfl, fun _ h => (by cases h)⟩

theorem TabRelM.ofH {syms R} (hR : IsSimMU syms R) {fr fr' : Frame} {et et' : ExnTable}
    (h : HContM syms R fr et fr' et') : TabRelM syms fr (some et) fr' (some et') := by
  intro e
  simp only [Option.bind]
  refine ⟨(h e).1, fun fr1 h1 => ?_⟩
  obtain ⟨fr1', h2, hj⟩ := (h e).2 fr1 h1
  exact ⟨fr1', h2, fun m hm => ⟨R, hR, .inr (hj.mono fun _ _ h => h m hm)⟩⟩

theorem TabRelM.bt {syms : String → Option Nat} {fr fr' : Frame} {t t' : Option ExnTable}
    (h : TabRelM syms fr t fr' t') (b b' : List Stmt) (tm tm' : Terminator) :
    TabRelM syms { fr with body := b, term := tm } t { fr' with body := b', term := tm' } t' := by
  intro e
  simp only [catchIn_bt]
  exact h e

/-- Suspended callers with their pending tables, related through their continuations and
handlers, at every memory with the symbols. -/
inductive CallersRelMU (syms : String → Option Nat) :
    List Ty → List (Frame × List ValueId) → List (Option ExnTable) →
      List (Frame × List ValueId) → List (Option ExnTable) → Prop
  | nil (rtys) : CallersRelMU syms rtys [] [] [] []
  | cons {rtys c rs t c' rs' t' cs ts cs' ts'} : ContM syms (GRMU syms) c rs c' rs' rtys →
      c'.slots = c.slots → TabRelM syms c t c' t' →
      CallersRelMU syms (AbiParam.tys c.func.sig.returns) cs ts cs' ts' →
      CallersRelMU syms rtys ((c, rs) :: cs) (t :: ts) ((c', rs') :: cs') (t' :: ts')

theorem CallersRelMU.length {syms rtys cs ts cs' ts'}
    (h : CallersRelMU syms rtys cs ts cs' ts') : cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

/-- Related states with unwinding, the frames related at the (common) memory. -/
structure SRMU (syms : String → Option Nat) (xs xs' : XState) : Prop where
  mem : xs'.s.mem = xs.s.mem
  symbols : xs.s.mem.symbols = syms
  frame : GRMU syms xs.s.frame xs'.s.frame xs.s.mem
  callers : CallersRelMU syms (AbiParam.tys xs.s.frame.func.sig.returns) xs.s.callers xs.tries
    xs'.s.callers xs'.tries

/-! ## From memory-blind relations -/

theorem GRU.toMU {syms : String → Option Nat} {fr fr' : Frame} (h : GRU syms fr fr') (m : Mem) :
    GRMU syms fr fr' m := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨_, hR.toMU, h⟩

theorem TabRel.toM {syms : String → Option Nat} {c c' : Frame} {t t' : Option ExnTable}
    (h : TabRel syms c t c' t') : TabRelM syms c t c' t' := by
  intro e
  refine ⟨(h e).1, fun fr1 h1 => ?_⟩
  obtain ⟨fr1', h2, hg⟩ := (h e).2 fr1 h1
  exact ⟨fr1', h2, fun m _ => hg.toMU m⟩

theorem CallersRelU.toMU {syms rtys cs ts cs' ts'} (h : CallersRelU syms rtys cs ts cs' ts') :
    CallersRelMU syms rtys cs ts cs' ts' := by
  induction h with
  | nil rtys => exact .nil rtys
  | cons hk hsl hT _ ih =>
    exact .cons (fun vs regs m ht _ hr => by
      obtain ⟨regs', h1, h2⟩ := hk vs regs ht hr
      exact ⟨regs', h1, h2.toMU m⟩) hsl hT.toM ih

/-- **Memory-blind related states are memory-aware related states.** -/
theorem SRU.toMU {syms : String → Option Nat} {xs xs' : XState} (h : SRU syms xs xs') :
    SRMU syms xs xs' :=
  ⟨h.mem, h.symbols, h.frame.toMU _, h.callers.toMU⟩

/-! ## Related step results -/

/-- Related step results with unwinding. -/
def XStepRelMU (syms : String → Option Nat) (r r' : XStepResult) : Prop :=
  (∀ xs1, r = .next xs1 → ∃ xs1', r' = .next xs1' ∧ SRMU syms xs1 xs1') ∧
    (∀ vs m, r = .done vs m → r' = .done vs m) ∧ (∀ c, r = .trapped c → r' = .trapped c) ∧
    (∀ e m, r = .unwound e m → r' = .unwound e m)

section
variable {syms : String → Option Nat} {n : Nat} {t t' : Option ExnTable}
  {ts ts' : List (Option ExnTable)}

theorem XStepRelMU.stuck' {msg : String} {r' : XStepResult} :
    XStepRelMU syms (liftWith n t ts (.stuck msg)) r' :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
    fun _ _ h => (by cases h)⟩

theorem XStepRelMU.trapped' {c : TrapCode} :
    XStepRelMU syms (liftWith n t ts (.trapped c)) (liftWith n t' ts' (.trapped c)) :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => h, fun _ _ h => (by cases h)⟩

theorem XStepRelMU.done' {vs : List Val} {m : Mem} :
    XStepRelMU syms (liftWith n t ts (.done vs m)) (liftWith n t' ts' (.done vs m)) :=
  ⟨fun _ h => (by cases h), fun _ _ h => h, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelMU.same' {s1 s1' : State} (h1 : s1.callers.length = n)
    (h2 : s1'.callers.length = n) (h : SRMU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) :
    XStepRelMU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_same h1, liftWith_same h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelMU.push' {s1 s1' : State} (h1 : s1.callers.length = n + 1)
    (h2 : s1'.callers.length = n + 1) (h : SRMU syms ⟨s1, t :: ts⟩ ⟨s1', t' :: ts'⟩) :
    XStepRelMU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_push h1, liftWith_push h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelMU.pop' {s1 s1' : State} (h1 : s1.callers.length + 1 = n)
    (h2 : s1'.callers.length + 1 = n) (h : SRMU syms ⟨s1, ts.tail⟩ ⟨s1', ts'.tail⟩) :
    XStepRelMU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_pop h1, liftWith_pop h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

end

/-! ## Calls, returns and tail calls -/

theorem funSimMU_entry {syms f g} (h : FunSimMU f g) {vals mem fr mem'}
    (hsym : mem.symbols = syms) (he : enterFunc f vals mem = .ok (fr, mem')) :
    ∃ fr', enterFunc g vals mem = .ok (fr', mem') ∧ GRMU syms fr fr' mem' ∧
      mem'.symbols = mem.symbols := by
  obtain ⟨b, regs, hb, h1, h2, hr, hsl, hfr⟩ := enterFunc_ok he
  obtain ⟨R, hR, hent⟩ := h.sim syms
  obtain ⟨b', hb', hp, hrel⟩ := hent b hb
  have hids := enterSlots_ids f mem
  rw [hsl] at hids
  refine ⟨⟨g, regs, fr.slots, b'.body, b'.term⟩, ?_, GRMU.of hR ?_, hids.2⟩
  · rw [enterFunc_of hb' (by rw [h.sig]; exact h1) (by rw [hp]; exact h2) (by rw [hp]; exact hr),
      enterSlots_congr h.name h.slots, hsl]
  · rw [hfr]; exact hrel vals regs fr.slots mem' h2 hr hids.1 (hids.2.trans hsym)

theorem returnValues_relMU {syms : String → Option Nat} {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {m : Mem} {vals : List Val} {mem0 : Mem}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hsym : mem0.symbols = syms) :
    XStepRelMU syms (liftWith s.callers.length t ts (returnValues s vals mem0))
      (liftWith s.callers.length t' ts' (returnValues ⟨fr2, cs', m⟩ vals mem0)) := by
  simp only [returnValues, hsig, hsl]
  by_cases hty : vals.map (·.ty) = AbiParam.tys s.frame.func.sig.returns
  · have hck : ∀ w, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .ok () := by
      intro w; simp [checkTys, hty]
    simp only [hck, StepResult.ofRes_ok]
    obtain ⟨frame, callers, mem⟩ := s
    simp only at hc ⊢
    cases hc with
    | nil => exact XStepRelMU.done'
    | @cons _ c rs t0 c' rs' t0' cs ts0 cs' ts0' hk hcsl hT hcs =>
      simp only
      cases hsm : c.regs.setMany rs vals with
      | none => exact XStepRelMU.stuck'
      | some regs =>
        have hm1 : ((mem0.free (frame.slots.map (·.2))).leave).symbols = syms :=
          (leave_free_symbols _ _).trans hsym
        obtain ⟨regs', hr', hg⟩ := hk vals regs _ hty hm1 hsm
        simp only [hr']
        exact XStepRelMU.pop' rfl (by simp [hcs.length]) ⟨rfl, hm1, hg, hcs⟩
  · have hck : ∀ w, ∃ m, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .stuck m := by
      intro w; simp [checkTys, hty, Res.check]
    obtain ⟨m1, h1⟩ := hck s!"return values of %{s.frame.func.name}"
    rw [h1]
    exact XStepRelMU.stuck'

theorem callCont_relMU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val} {rs rs' : List ValueId}
    {rest rest' : List Stmt} {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hk : ContM syms (GRMU syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys ext.sig.returns))
    (hsl : fr2.slots = s.frame.slots)
    (hT : TabRelM syms { s.frame with body := rest } t { fr2 with body := rest' } t') :
    XStepRelMU syms (liftWith s.callers.length t ts (callCont env p s rest rs ext vals))
      (liftWith s.callers.length t' ts' (callCont env q ⟨fr2, cs', s.mem⟩ rest' rs' ext vals)) := by
  have hlen := hc.length
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  simp only [callCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig]
    split
    · rename_i hcond
      cases he : enterFunc callee vals s.mem with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact XStepRelMU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimMU_entry hfs hsym he
        simp only [he', StepResult.ofRes_ok]
        have hret : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelMU.push' (by simp) (by simp [hlen]) ⟨rfl, hsy.trans hsym, hg, ?_⟩
        simp only
        rw [hfr]
        exact .cons (by rw [hret]; exact hk) hsl hT hc
    · exact XStepRelMU.stuck'
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact XStepRelMU.stuck'
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact XStepRelMU.trapped'
      | stuck m => exact XStepRelMU.stuck'
      | outOfFuel => exact XStepRelMU.stuck'
      | returned rvals mem' =>
        simp only
        split
        · rename_i hty
          simp only [beq_iff_eq] at hty
          simp only [continueWith]
          cases hsm : s.frame.regs.setMany rs rvals with
          | none => exact XStepRelMU.stuck'
          | some regs =>
            have hm1 : mem'.symbols = syms := (hE _ _ hx _ _ _ _ hr).trans hsym
            obtain ⟨regs', hr', hg⟩ := hk rvals regs mem' hty hm1 hsm
            simp only at hr'
            simp only [hr']
            exact XStepRelMU.same' rfl hlen ⟨rfl, hm1, hg, hc⟩
        · exact XStepRelMU.stuck'

theorem tailCont_relMU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hret : AbiParam.tys ext.sig.returns = AbiParam.tys s.frame.func.sig.returns) :
    XStepRelMU syms (liftWith s.callers.length t ts (tailCont env p s ext vals))
      (liftWith s.callers.length t' ts' (tailCont env q ⟨fr2, cs', s.mem⟩ ext vals)) := by
  have hlen := hc.length
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  simp only [tailCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig, hsl]
    split
    · rename_i hcond
      cases he : enterFunc callee vals (s.mem.free (s.frame.slots.map (·.2))).leave with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact XStepRelMU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        have hm0 : ((s.mem.free (s.frame.slots.map (·.2))).leave).symbols = syms :=
          (leave_free_symbols _ _).trans hsym
        obtain ⟨frc', he', hg, hsy⟩ := funSimMU_entry hfs hm0 he
        simp only [he', StepResult.ofRes_ok]
        have hr2 : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelMU.same' rfl hlen ⟨rfl, hsy.trans hm0, hg, ?_⟩
        simp only
        rw [hfr]
        simp only
        rw [hr2, hret]
        exact hc
    · exact XStepRelMU.stuck'
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact XStepRelMU.stuck'
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact XStepRelMU.trapped'
      | stuck m => exact XStepRelMU.stuck'
      | outOfFuel => exact XStepRelMU.stuck'
      | returned rvals mem' =>
        exact returnValues_relMU hsig hsl hc ((hE _ _ hx _ _ _ _ hr).trans hsym)

theorem ciCont_relMU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {sig sig' : Nat} {d : Signature} {a : Nat}
    {vals : List Val} {rs rs' : List ValueId} {rest rest' : List Stmt}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hk : ContM syms (GRMU syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys d.returns))
    (hsl : fr2.slots = s.frame.slots)
    (hT : TabRelM syms { s.frame with body := rest } t { fr2 with body := rest' } t') :
    XStepRelMU syms (liftWith s.callers.length t ts (ciCont env p s rest rs sig d a vals))
      (liftWith s.callers.length t' ts'
        (ciCont env q ⟨fr2, cs', s.mem⟩ rest' rs' sig' d a vals)) := by
  have hlen := hc.length
  obtain ⟨hs, hn⟩ := hP.findP (fun n => s.mem.symbols n == some a)
  simp only [ciCont]
  cases hpf : p.funcs.find? (fun f => s.mem.symbols f.name == some a) with
  | some target =>
    obtain ⟨target', hq, hfs⟩ := hs target hpf
    simp only [hq, hfs.sig]
    split
    · rename_i hcond
      cases he : enterFunc target vals s.mem with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact XStepRelMU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimMU_entry hfs hsym he
        simp only [he', StepResult.ofRes_ok]
        have hret : AbiParam.tys d.returns = AbiParam.tys target.sig.returns :=
          (Signature.abiMatch_eq_true.1 hcond).2.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelMU.push' (by simp) (by simp [hlen]) ⟨rfl, hsy.trans hsym, hg, ?_⟩
        simp only
        rw [hfr]
        exact .cons (by rw [← hret]; exact hk) hsl hT hc
    · exact XStepRelMU.stuck'
  | none =>
    simp only [hn hpf, callExternAt_congr (env := env) (FunsSimMU.externNames hP)]
    cases hx : callExternAt env p s.mem d a vals with
    | trap c => exact XStepRelMU.trapped'
    | stuck m => exact XStepRelMU.stuck'
    | ok x =>
      obtain ⟨rvals, mem'⟩ := x
      simp only [StepResult.ofRes_ok, continueWith]
      cases hsm : s.frame.regs.setMany rs rvals with
      | none => exact XStepRelMU.stuck'
      | some regs =>
        have hm1 : mem'.symbols = syms := (callExternAt_symbols hE hx).trans hsym
        obtain ⟨regs', hr', hg⟩ := hk rvals regs mem' (callExternAt_tys hx) hm1 hsm
        simp only at hr'
        simp only [hr']
        exact XStepRelMU.same' rfl hlen ⟨rfl, hm1, hg, hc⟩

/-! ## Steps where no callee unwinds -/

/-- One source step whose head is not a `call_indirect` nor a `try_call`
(`sim_step_lstepU` with the memory). -/
theorem sim_step_lstepMU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {R : Frame → Frame → Mem → Prop}
    (hR : IsSimMU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hr : R s.frame fr' s.mem) (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hci : HeadNoCI s.frame) :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q ⟨fr', cs', s.mem⟩ s1' ∧
      s1.callers = s.callers ∧ SRMU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) ∨
    (∃ s2, Stut env q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelMU syms (liftWith s.callers.length (pendingOf s) ts (step env p s))
        (liftWith s.callers.length (pendingOf s2) ts' (step env q s2))) := by
  have hS := hR.toIsSimM
  have hsl0 := (hS.frame hr).1
  rw [step_eq_lift env p s hci]
  cases hl : lstep s.frame s.mem with
  | next fr1 m1 =>
    left
    obtain ⟨fr1', hst, hr1⟩ := hS.next hr hsym hl
    have hf := lstep_next_frame hl
    refine ⟨_, ⟨fr1', cs', m1⟩, rfl, hst.stut cs', rfl, rfl, hf.2.2.trans hsym,
      GRMU.of hR hr1, ?_⟩
    simp only [hf.1]; exact hc
  | call ext vals rs rest =>
    right
    obtain ⟨fr2, rs', rest', hst, hl2, hk⟩ := hS.call hr hsym hl
    obtain ⟨st, fn, args, hb, -, -, -⟩ := lstep_call_inv hl
    obtain ⟨st', fn', args', hb2, -, -, -⟩ := lstep_call_inv hl2
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h),
      pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
    simp only [LRes.lift]
    exact callCont_relMU hE hP hsym hc (hk.mono fun a b m h => GRMU.of hR h)
      (by rw [(LStar.frame hst).2.1, hsl0]) (TabRelM.none' _ _ _)
  | ret vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.ret hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact returnValues_relMU (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1) hc hsym
  | tail ext vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.tail hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact tailCont_relMU hE hP hsym hc (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1)
      (lstep_tail_returns hl)
  | trap c =>
    right
    obtain ⟨fr2, m2, hst, hl2⟩ := hS.trap hr hsym hl
    refine ⟨⟨fr2, cs', m2⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', m2⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    exact XStepRelMU.trapped'
  | stuck m =>
    right
    exact ⟨_, .refl _, XStepRelMU.stuck'⟩

/-- **One source step where no callee unwinds** (`sim_stepU_core` with the memory). -/
theorem sim_stepMU_core {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {R : Frame → Frame → Mem → Prop}
    (hR : IsSimMU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hfr : R s.frame fr' s.mem ∨ JR (fun x y => R x y s.mem) s.frame fr')
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts') :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q ⟨fr', cs', s.mem⟩ s1' ∧
      s1.callers = s.callers ∧ SRMU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) ∨
    (∃ s2, Stut env q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelMU syms (liftWith s.callers.length (pendingOf s) ts (step env p s))
        (liftWith s.callers.length (pendingOf s2) ts' (step env q s2))) := by
  have hlen := hc.length
  rcases hfr with hr | ⟨hb, hb', bc, bc', ht, ht', hj⟩
  · have hsl0 := (hR.toIsSimM.frame hr).1
    by_cases hci : HeadNoCI s.frame
    · exact sim_step_lstepMU hE hP hR hr hsym hc hci
    right
    cases hb : s.frame.body with
    | cons st rest =>
      have : ∃ sig callee args, st.inst = .callIndirect sig callee args := by
        apply Classical.byContradiction
        intro hn
        refine hci ⟨fun st' rest' hb' sig callee args hi => ?_, fun h => by rw [hb] at h; cases h⟩
        rw [hb] at hb'; cases hb'
        exact hn ⟨sig, callee, args, hi⟩
      obtain ⟨sig, callee, args, hi⟩ := this
      rw [step_callIndirect' hb hi, stepCallIndirect_eq, pendingOf_cons (s := s) hb]
      cases hca : ciArgs s.frame sig callee args with
      | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
      | stuck msg => exact ⟨_, .refl _, XStepRelMU.stuck'⟩
      | ok x =>
        obtain ⟨d, a, vals⟩ := x
        obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, hk⟩ :=
          hR.ci hr hsym hb hi hca
        refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
        rw [step_callIndirect' (s := ⟨fr2, cs', s.mem⟩) hb2 hi2, stepCallIndirect_eq,
          pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        simp only [hca2, StepResult.ofRes_ok]
        exact ciCont_relMU hE hP hsym hc (hk.mono fun a b m h => GRMU.of hR h)
          (by rw [(LStar.frame hst).2.1, hsl0]) (TabRelM.none' _ _ _)
    | nil =>
      have hT : s.frame.term.isTry = true := by
        cases h2 : s.frame.term.isTry
        · exact absurd (show HeadNoCI s.frame from
            ⟨fun st rest h => (by rw [hb] at h; cases h), fun _ => h2⟩) hci
        · rfl
      rw [step_term env p s hb]
      cases ht : s.frame.term with
      | tryCall fn args et =>
        rw [pendingOf_try hb ht]
        simp only [stepTerm]
        rw [stepTryCall_eq]
        cases htc : tcArgs s.frame fn et with
        | trap c => exact absurd htc (tcArgs_ne_trap _ _ _ _)
        | stuck msg => exact ⟨_, .refl _, XStepRelMU.stuck'⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : callArgs s.frame fn args with
          | trap c => exact absurd hca (callArgs_ne_trap _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, XStepRelMU.stuck'⟩
          | ok y =>
            obtain ⟨ext, vals⟩ := y
            obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
              hR.tc.call hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2,
              pendingOf_try (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
            simp only [ht2, stepTerm]
            rw [stepTryCall_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact callCont_relMU (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toContMU hR)
              (show fr2.slots = s.frame.slots by rw [(LStar.frame hst).2.1, hsl0])
              ((TabRelM.ofH hR hh).bt [] [] (.jump bc) (.jump bc'))
      | tryCallIndirect callee args et =>
        rw [pendingOf_tryInd hb ht]
        simp only [stepTerm]
        rw [stepTryCallIndirect_eq]
        cases htc : ticArgs s.frame et with
        | trap c => exact absurd htc (ticArgs_ne_trap _ _ _)
        | stuck msg => exact ⟨_, .refl _, XStepRelMU.stuck'⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : ciArgs s.frame et.sig callee args with
          | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, XStepRelMU.stuck'⟩
          | ok y =>
            obtain ⟨d, a, vals⟩ := y
            obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
              hR.tc.ind hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2,
              pendingOf_tryInd (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
            simp only [ht2, stepTerm]
            rw [stepTryCallIndirect_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact ciCont_relMU (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toContMU hR)
              (show fr2.slots = s.frame.slots by rw [(LStar.frame hst).2.1, hsl0])
              ((TabRelM.ofH hR hh).bt [] [] (.jump bc) (.jump bc'))
      | _ => rw [ht] at hT; simp [Terminator.isTry] at hT
  · right
    refine ⟨⟨fr', cs', s.mem⟩, .refl _, ?_⟩
    rw [step_term env p s hb, step_term env q ⟨fr', cs', s.mem⟩ hb']
    simp only [ht, ht', stepTerm]
    cases he : enterBlock s.frame bc with
    | trap c => exact absurd he (enterBlock_not_trap _ _ _)
    | stuck m => exact XStepRelMU.stuck'
    | ok a1 =>
      obtain ⟨b1, hb1, hr1⟩ := hj a1 he
      simp only [hb1, StepResult.ofRes_ok]
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := enterBlock_ok he
      exact XStepRelMU.same' rfl hlen ⟨rfl, hsym, GRMU.of hR hr1, hc⟩

end Opt
