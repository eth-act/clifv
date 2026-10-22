import FV.Concurrency.ArmAllocLoop
import FV.Concurrency.ArmAllocFwd

/-!
# Precise runs through the `atomic_rmw` loop, forward (T2m, #311)

`ArmAllocFwd` builds precise runs of compiled code forward through lines without a store
exclusive. The `atomic_rmw` loop ends in an `stlxr`, which succeeds only with the local monitor
armed (`Policy.arm`); here the monitor is tracked:

* `step_fwdS`: one precise step at an unhooked line, a store exclusive allowed when the monitor
  is armed; the monitor after it is `monAfter`;
* `prun_quiet`: through steps without events of class `plain`, the monitor kept;
* `rmw_at`, `rmw_fwd`: from the loop label, the `ldaxr` (arming the monitor, one `acqXR` read of
  the bytes at x25), the middle (no events) and the successful `stlxr` (one `relXW` write of
  `rmwNew` at x25), as one precise run reading the thread's own bytes (`OkPriv`);
* `rmw_lines`: at a `Q`-related state before an allocated `atomic_rmw` loop item, the loop's lines
  are at the pc.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents VCodeAddr ArmLoop IselMemAux

/-- The monitor after a step that is no failing store exclusive. -/
theorem tstep_mon {P : Policy} {f : ArmState → ArmState} {s : ArmState} {mon : Mon} {l : Lab}
    {t1 : ArmState × Mon} (hs : TStep P f (s, mon) l t1) (hx : l.xfail = false) :
    t1.2 = monAfter (cls s) s mon := by
  cases hs with
  | exec => rfl
  | xfail => cases hx

/-- **One precise step at an unhooked line**, a store exclusive with the monitor armed, reading
the thread's own memory: its label the single-core step's events, its state the single-core
step's, its monitor `monAfter`. -/
theorem step_fwdS {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t))
    (hh : x.hooked = false) (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.pcOf j) (herr : Arm.r .ERR s = .None) (mon : Mon)
    (hsucc : ∀ rel rs rn, cls s = .stx rel rs rn → mon.isSome = true) :
    ∃ t1 : ArmState × Mon, PRun Policy.arm R.step (OkPriv R) (s, mon) [⟨stepEvs s, false⟩] t1 ∧
      t1.1 = R.step s ∧ t1.2 = monAfter (cls s) s mon := by
  obtain ⟨a0, ha0, -, -, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh
    hprog hpc herr
  obtain ⟨a, t'', ha, -, hr⟩ := exists_prun_lineS hR hj hh hprog hpc herr mon
    (fun a' ha' rel rs rn hc => by
      rw [show R.envOf j = ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ from rfl, ha0] at ha'
      cases ha'
      exact hsucc rel rs rn (by rw [cls_of_decode hdec]; exact hc)) s.mem
  rw [setMem_self] at hr
  cases hr with
  | cons hs hp _ hr' =>
    cases hr'
    obtain ⟨h1, -, -⟩ := tstep_own hs hp (ArmPrecise.agrees_stepEvs s) rfl
    exact ⟨_, .cons hs hp (fun e he hR' _ => ArmPrecise.agrees_stepEvs s e he hR') .nil, h1,
      tstep_mon hs rfl⟩

/-- **Through `c` steps without events of class `plain`**: the precise run with empty labels,
the monitor kept. -/
theorem prun_quiet {R : RL} (hR : R.Wf) :
    ∀ (c : Nat) (u : ArmState) (mon : Mon),
      (∀ i < c, ∃ j x tc, R.fa.lines.toList[j]? = some (.ins x tc) ∧ x.hooked = false ∧
        (iterN R.step i u).program = R.fb.program R.base ∧
        Arm.r .PC (iterN R.step i u) = R.pcOf j ∧ Arm.r .ERR (iterN R.step i u) = .None ∧
        cls (iterN R.step i u) = .plain ∧ stepEvs (iterN R.step i u) = []) →
      PRun Policy.arm R.step (OkPriv R) (u, mon) (List.replicate c ⟨[], false⟩)
        (iterN R.step c u, mon)
  | 0, _, _, _ => .nil
  | c + 1, u, mon, h => by
    obtain ⟨j, x, tc, hj, hh, hp, hpc, he, hc, hev⟩ := h 0 (by omega)
    simp only [iterN] at hp hpc he hc hev
    obtain ⟨t1, r1, e1, e2⟩ := step_fwdS hR hj hh hp hpc he mon
      (fun rel rs rn h' => by rw [hc] at h'; cases h')
    rw [hc] at e2
    have ht1 : t1 = (R.step u, mon) := Prod.ext e1 e2
    subst ht1
    rw [hev] at r1
    exact PRun.append r1 (prun_quiet hR c (R.step u) mon fun i hi => h (i + 1) (by omega))

/-- The lines and the states of the `atomic_rmw` loop's body, from its first line. -/
theorem rmw_at {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {j0 n : Nat} {T : List Line}
    (hd1 : R.L.drop (j0 + 1) =
      rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T))
    {s : ArmState} (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf (j0 + 1))
    (herr : Arm.r .ERR s = .None) (i : Nat) (hi : i < (rmwLoopMid op ty.bits).length + 2) :
    ∃ x tc, R.fa.lines.toList[j0 + 1 + i]? = some (.ins x tc) ∧ x.hooked = false ∧
      (rmwLoopBody ty.bits op fl)[i]? = some (.ins x tc) ∧
      (iterN R.step i s).program = R.fb.program R.base ∧
      Arm.r .PC (iterN R.step i s) = R.pcOf (j0 + 1 + i) ∧
      Arm.r .ERR (iterN R.step i s) = .None := by
  have hlen := rmwBody_len ty.bits op fl
  obtain ⟨t', hrun, hint, -⟩ := rmwBody_spec hty op fl (R.envOf (j0 + 1)) s herr
  have hat := lines_at' hd1
  obtain ⟨ln, hln⟩ : ∃ ln, (rmwLoopBody ty.bits op fl)[i]? = some ln :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, tc, rfl, hh⟩ := rmwBody_ins hty op fl _ (List.mem_of_getElem? hln)
  refine ⟨x, tc, hat i _ hln, hh, hln, ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact ⟨hprog, by rw [Nat.add_zero]; exact hpc, herr⟩
  obtain ⟨s1, hs1⟩ := execLines_take hrun i
  have hd' : R.L.drop (j0 + 1) = (rmwLoopBody ty.bits op fl).take i ++
      ((rmwLoopBody ty.bits op fl).drop i ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T)) := by
    rw [hd1, ← List.append_assoc, List.take_append_drop]
  obtain ⟨hit, hpcs, -⟩ := run_ins hR hd'
    (fun l hl => rmwBody_ins hty op fl l (List.mem_of_mem_take hl)) hprog hpc herr
    (interOk_take hint i) hs1
  rw [List.length_take, Nat.min_eq_left (by omega)] at hit hpcs
  obtain ⟨he, hp⟩ := hint i h0 (by omega) s1 hs1
  rw [hit]
  exact ⟨hp.trans hprog, hpcs, he⟩

/-- **The `atomic_rmw` loop, forward, one successful iteration**: from a state at the loop label,
for every monitor, the precise run reading the thread's own bytes through the `ldaxr` (one
`acqXR` read of the bytes at x25), the middle (no events) and the successful `stlxr` (one `relXW`
write of `rmwNew` at x25); after it, the single-core state and an open monitor. -/
theorem rmw_fwd {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {j0 n : Nat} {T : List Line}
    (hd1 : R.L.drop (j0 + 1) =
      rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T))
    (hL0 : R.L[j0]? = some (.label (.loop n)))
    {s : ArmState} (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (mon : Mon) :
    PRun Policy.arm R.step (OkPriv R) (s, mon)
      (⟨[loopRd ty s s], false⟩ :: (List.replicate (rmwLoopMid op ty.bits).length ⟨[], false⟩ ++
        [⟨[⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes, rmwNew ty op s⟩], false⟩]))
      (R.step (iterN R.step ((rmwLoopMid op ty.bits).length + 1) s), none) := by
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  obtain ⟨t', -, -, ⟨hev0, -⟩, hmid, hwev, hcls, -⟩ := rmw_steps hR hty hd1 hL0 hprog hpc1 herr
  generalize hM : (rmwLoopMid op ty.bits).length = M at hmid hwev hcls ⊢
  have hat := rmw_at hR hty hd1 hprog hpc1 herr
  rw [hM] at hat
  -- the `ldaxr`
  obtain ⟨x0, tc0, hj0, hh0, hb0, -, -, -⟩ := hat 0 (by omega)
  rw [rmwBody_get0] at hb0
  simp only [Option.some.injEq, Line.ins.injEq] at hb0
  obtain ⟨rfl, rfl⟩ := hb0
  obtain ⟨a0, ha0, -, -, hdec0⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj0
    hh0 hprog hpc1 herr
  obtain ⟨sz, hsz⟩ := ldaxr_cls hty ha0
  have hc0 : cls s = .ldx true 25#5 sz := by rw [cls_of_decode hdec0, hsz]
  obtain ⟨t1, r1, e11, e12⟩ := step_fwdS hR hj0 hh0 hprog hpc1 herr mon
    (fun rel rs rn h => by rw [hc0] at h; cases h)
  rw [hc0] at e12
  have ht1 : t1 = (R.step s, some (read_gpr 64 25#5 s, 2 ^ sz.toNat)) := Prod.ext e11 e12
  subst ht1
  rw [hev0] at r1
  -- the middle
  have r2 := prun_quiet hR M (R.step s) (some (read_gpr 64 25#5 s, 2 ^ sz.toNat)) fun i hi => by
    obtain ⟨x, tc, hj, hh, hb, hp, hpc', he⟩ := hat (i + 1) (by omega)
    obtain ⟨a, ha, -, -, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh
      hp hpc' he
    have hk := rmwBody_getMid (by omega) (by rw [hM]; omega) hb
    exact ⟨_, x, tc, hj, hh, hp, hpc', he, (cls_of_decode hdec).trans (clsOf_none ha hk),
      (hmid (i + 1) (by omega) (by omega)).1⟩
  -- the `stlxr`
  obtain ⟨x2, tc2, hj2, hh2, -, hp2, hpc2, he2⟩ := hat (M + 1) (by omega)
  obtain ⟨t3, r3, e31, e32⟩ := step_fwdS hR hj2 hh2 hp2 hpc2 he2
    (some (read_gpr 64 25#5 s, 2 ^ sz.toNat)) (fun _ _ _ _ => rfl)
  rw [hcls] at e32
  have ht3 : t3 = (R.step (iterN R.step (M + 1) s), none) := Prod.ext e31 e32
  subst ht3
  rw [hwev] at r3
  exact PRun.append r1 (PRun.append r2 r3)

/-- **The lines at an allocated `atomic_rmw` loop item**: at a `Q`-related state before it, the
loop label at line `j0` (the pc), its body and `cbnz` after it. -/
theorem rmw_lines {R : RL} (hR : R.Wf) {s : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState} (hq : Q R s (OpC b k allocs its m w))
    {vb : VBlock} {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {ra ro rd r1 r2 : Reg}
    (hty : AtomTy ty) (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicRmwLoop ty op fl ra ro rd r1 r2)) :
    ∃ j0 n T, R.L.drop (j0 + 1) =
        rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T) ∧
      R.L[j0]? = some (.label (.loop n)) ∧ s.program = R.fb.program R.base ∧
      Arm.r .PC s = R.pcOf j0 ∧ Arm.r .ERR s = .None ∧ StRel R s m w := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨vo, rfl⟩ := isVregInt_iff h1
  obtain ⟨vd, rfl⟩ := isVregInt_iff h2
  obtain ⟨v1, rfl⟩ := isVregInt_iff h3
  obtain ⟨v2, rfl⟩ := isVregInt_iff h4
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
      ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := by
    have e : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
        (.vreg v1 .int) (.vreg v2 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
          ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
  obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
  obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨vo, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
  obtain rfl : q2 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
  obtain rfl : q3 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
  obtain rfl : q4 = .x 28 := fixed_reg (o := ⟨v2, .int, .def, .late, .fixed (.x 28)⟩) hloc (by simp) rfl
  have hasg' : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int)).assign #[.x 25, .x 26, .x 27, .x 24, .x 28] =
      .ok (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  have hdrop' := ftList_rmw hR hty ⟨_, rfl⟩ hdrop
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
        (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
  exact ⟨j0, _, _, hd1, hL0, hst.prog, hpc, hst.err, hst⟩

end Concurrency.ArmAllocThread
