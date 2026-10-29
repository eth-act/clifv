import FV.Concurrency.RealizeWitnessFence
import FV.Concurrency.RealizeExec

/-!
# `Realizes` on a run of compiled code through its `ldar` (T2l, #311)

The CLIF function `%ld(i64) -> i64 { v1 = atomic_load.i64 v0; return v1 }` (`fL`) as the
pipeline compiles it (`lowerFunction`, `prepare`, `spillAlloc`; the activation `RL` as
`ArmAllocThread.Witness.act` loads it): after the 18 saves of the callee-saved registers, the
entry `args`, the spill of `x0` to its slot and back, and the `ldar x1, [x0]`.

* `compiled_ofL`: **every premise of `RealizeCompiled.Compiled`** for `RL`, the CLIF entry state
  `csL` (block 0, `v0 = 0`, an 8-byte allocation at address 0) and the Arm state after the
  prologue;
* `realizes_load`: the precise run (reading the thread's own bytes, `OkPriv`) through the saves
  (`moves_fwdA`), the `args` (a step of the allocated code without code, `realizes_args`), the
  spill moves (`moves_fwd`) and the `ldar` (`excl_step_fwd`: one `acqR` event of 8 bytes).
  Every event before the `ldar` is private (plain, in the frame); with the initial locations the
  `ldar`'s location (the CLIF one) and then the private events' locations, every execution of the
  realized prefix with reads from the latest earlier write (`wf_single`) is `Realizes`d by a CLIF
  thread from `csL` (`realizes_compiled`), for every initial memory.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessL

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E ArmInstFoot Code RealizeCompiled.Witness

/-! ## `atomic_load`, compiled -/

/-- `atomic_load.i64` of the argument. -/
def srcL : String := "function %ld(i64) -> i64 {
block0(v0: i64):
    v1 = atomic_load.i64 v0
    return v1
}
"

/-- The parsed function. -/
def fL : Clif.Function :=
  match Clif.parse srcL with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcL : VCode := match lowerFunction fL with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpL : VCode := match Backend.prepare vcL with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation. -/
def rfL : RFunc := spillAlloc vcpL

/-- The activation, entered with `sp = 0x6000`, its code at `0x20000` (frame and code disjoint
from `act`'s). -/
abbrev RAL : RL := ArmAllocThread.Witness.actAt 0x6000#64 0x20000#64 vcpL rfL

theorem checksL : lowerCheck fL vcL = true ∧ IselCheck.threadCheck fL = true ∧
    fL.externs.isEmpty = true ∧ (indSigs fL).isEmpty = true ∧ verifiable fL = true ∧
    IselThread.Witness.isOkB vcL.cfg = true ∧ vcL.outgoing = 0 ∧ prepCheck vcL vcpL = true ∧
    (checkAlloc vcpL rfL).isOk = true ∧ rfL.blocks.size = 1 ∧ (rfL.blocks[0]!).size = 43 := by
  native_decide

theorem allocL : checkAlloc vcpL rfL = .ok () := by
  have h := checksL.2.2.2.2.2.2.2.2.1
  revert h
  cases checkAlloc vcpL rfL with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem cfgL : ∃ ss ps, vcL.cfg = .ok (ss, ps) := by
  have hb := checksL.2.2.2.2.2.1
  revert hb
  cases vcL.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem factsL : (lowerRFunc vcpL rfL).toBool = true ∧ (emitFunc 0 RAL.af).toBool = true ∧
    RAL.fa.k = 0 ∧ RAL.fa.layout.toBool = true ∧ (labelOffsets RAL.fa.lines).toBool = true ∧
    4 * RAL.fb.words.size ≤ 2 ^ 64 ∧ RAL.af.frameSize ≤ 0x100 ∧ 4 * RAL.fb.words.size ≤ 0x10000 ∧
    (emitPlan RAL.fa.k RAL.af).toBool = true := by
  native_decide

theorem wfRL : RAL.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsL
  exact ArmAllocThread.Witness.wf_ofAt (by decide) (by decide) (by decide) (by decide) allocL h1 h2
    h3 h4 h5 h6 h7 h8 h9

theorem codeRL : ∀ k < RAL.fb.words.size,
    Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAL.s0 = RAL.fb.words[k]! := by
  native_decide

/-- The entry `args` of `vc` reads argument registers only. -/
def entryArgsB (vc : VCode) : Bool :=
  match vc.blocks[0]? with
  | some vb => match vb.insts[0]? with
    | some (MInst.args ds) => ds.all (·.2.isArgReg)
    | _ => true
  | none => true

theorem entryArgRL : ∀ r, RAL.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpL = true := by native_decide
  simp only [entryArgsB, show vcpL = RAL.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The entry world of the body. -/
abbrev w₀L : ArmState := E2E.bodyOf RAL.af RAL.s0

theorem qRL : ∃ n, Q RAL (iterN RAL.step n RAL.s0)
      (MConf.init RAL.rf (locVal RAL.fr (iterN RAL.step n RAL.s0)) w₀L) ∧
    AInv RAL (MConf.init RAL.rf (locVal RAL.fr (iterN RAL.step n RAL.s0)) w₀L) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRL
    (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsL.2.2.2.2.2.2.2.1 codeRL)
    ((E2E.Binary.bodyEntry_bodyOf RAL.af RAL.s0).w RAL.F entryArgRL)
  exact ⟨n, hq, hA⟩

/-- The memory forms `MemScope` admits, as a check (with `ldar`). -/
def memFormLB (ctx : FnCtx) : MInst → Bool
  | .fence | .args _ | .rets _ => true
  | i@(.loadAcquire ..) => FormOk ctx i
  | _ => false

theorem scopeRL : MemScope RAL := by
  have h : RAL.vc.blocks.all (·.insts.all (memFormLB RAL.ctx)) = true := by native_decide
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize RAL.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inr (.inl rfl)
  | args ds => exact .inl (.inr (.inl ⟨ds, rfl⟩))
  | rets us => exact .inl (.inr (.inr (.inl ⟨us, rfl⟩)))
  | loadAcquire ty rt rn fl => exact .inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩))
  | _ => simp [memFormLB] at h2

/-! ## The CLIF entry -/

/-- The function's entry block. -/
def B0L : Clif.Block := fL.blocks.headD default

/-- The argument: `0 : i64` (`x0` at the entry). -/
def argsL : List Clif.Val := [⟨.i64, 0⟩]

/-- The entry registers: `v0 = 0`. -/
def regsL : Clif.Regs := (Clif.Regs.empty.setMany (B0L.params.map (·.1)) argsL).getD Clif.Regs.empty

/-- The CLIF memory: one 8-byte allocation at address 0 (no initialised byte). -/
def memL : Clif.Mem := { allocs := [⟨0, 8, false⟩] }

/-- **The CLIF entry state**: block 0, `v0 = 0`, no slots, `memL`. -/
def csL : Clif.State :=
  { frame := { func := fL, regs := regsL, slots := [], body := B0L.body, term := B0L.term }
    callers := []
    mem := memL }

/-- The memory relation's parameters (as `ΓF`). -/
def ΓL : E2E.Rel := ⟨RAL.F, fun _ => none, RAL.ctx.slotBase, 0⟩

theorem shapeL : fL.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0L.params.map (·.1)) argsL).isSome = true ∧
    argsL.map (·.ty) = B0L.params.map (·.2) ∧ argsL.map (·.ty) = fL.sig.params.map (·.ty) ∧
    (locsOf fL.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    (match locsOf fL.sig with | [.reg (.x 0)] => true | _ => false) = true ∧
    (E2E.spv w₀L).toNat % 16 = 0 ∧ regVal RAL.s0 (.x 0) = 0 := by
  native_decide

theorem b0L : fL.blocks[0]? = some B0L := by
  have h := shapeL.1
  unfold B0L
  revert h
  cases fL.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsL_eq : Clif.Regs.empty.setMany (B0L.params.map (·.1)) argsL = some regsL := by
  have h := shapeL.2.1
  unfold regsL
  revert h
  cases Clif.Regs.empty.setMany (B0L.params.map (·.1)) argsL with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem errW₀L : Arm.r .ERR w₀L = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsL.2.2.2.2.2.2.2.1 codeRL).err

/-- The frame addresses of an activation, as a check. -/
def fB (R : Backend.Proof.RL) (a : BitVec 64) : Bool :=
  let d := (a - (spv R.s0 - BitVec.ofNat 64 (frameDrop R.af))).toNat
  (decide (R.fr.intBase ≤ d) && decide (d < R.fr.size)) ||
    (decide (R.af.frameSize - clobberBytes R.af.saves ≤ d) && decide (d < frameDrop R.af)) ||
    R.s0.program.any (fun p => decide ((a - p.1).toNat < 4))

theorem fB_of {R : Backend.Proof.RL} (hK : R.K = 0) (hG : ∀ a, ¬ R.G a) {a : BitVec 64}
    (h : R.F a) : fB R a = true := by
  unfold Backend.Proof.RL.F frameWG frameW frameF StackBelow CodeAddr at h
  simp only [fB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  rcases h with ((h | h | h) | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr h)
  · obtain ⟨p, hp, hd⟩ := h
    exact .inr (List.any_eq_true.mpr ⟨p, hp, by simpa using hd⟩)
  · exfalso
    obtain ⟨h1, h2⟩ := h
    omega
  · exact (hG _ h).elim

/-- **The first 8 bytes are no frame address.** -/
theorem notF_low : ∀ x < 8, ¬ RAL.F (BitVec.ofNat 64 x) := by
  have h : ∀ x < 8, fB RAL (BitVec.ofNat 64 x) = false := by native_decide
  intro x hx hF
  have := h x hx
  rw [fB_of rfl (fun _ h => h) hF] at this
  cases this

theorem relL : E2E.RelW ΓL fL (E2E.spv w₀L) [] memL w₀L := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀L⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  exact ⟨by omega, fun k hk => notF_low _ (by omega)⟩

theorem locsL : locsOf fL.sig = [.reg (.x 0)] := by
  have h := shapeL.2.2.2.2.2.1
  revert h
  generalize locsOf fL.sig = l
  intro h
  match l, h with
  | [.reg (.x 0)], _ => rfl

theorem argsAtL : ArgsAtEntry RAL.F fL.sig argsL w₀L := by
  intro loc v h
  rw [locsL] at h
  simp only [argsL, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  show VHolds _ _
  rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeL.2.2.2.2.2.2.2]
  rfl

/-- `Compiled` for the compiled `atomic_load` at every Arm state `Q`-related to its entry
configuration. -/
theorem compiled_ofL {s : ArmState} (hq : Q RAL s (MConf.init RAL.rf (locVal RAL.fr s) w₀L))
    (hA : AInv RAL (MConf.init RAL.rf (locVal RAL.fr s) w₀L)) (env : Clif.Env) (p : Clif.Program) :
    Compiled env p RAL csL s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksL
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓL) (fctx := RAL.ctx) (X := RAL.X)
    (c := E2E.spv w₀L) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgL hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, hc, -⟩ := shapeL
  exact {
    wf := wfRL
    scope := scopeRL
    gv := rfl
    front := ⟨fL, vcL, ctx, st0, R, gn, bl, A, _, [], ΓL.slotOff, ΓL.syms, B0L, argsL, _, w₀L, H,
      hbl, E2E.memRelOk_relW ΓL fL _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RAL.F RAL.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓL fL _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocL, b0L, rfl, rfl, rfl, rfl, rfl, regsL_eq, hpar, hsig, relL, argsAtL, hq, hA⟩ }


/-! ## One compiled thread, its private prefix and one shared access -/

/-- The Arm thread of the realized prefix of `ls` from `sA`. -/
noncomputable def PA1 (RA : Backend.Proof.RL) (sA : ArmState) (ls : List Lab) (k : Nat) :
    Traces ProgE2E.AState AKind BVal :=
  ⟨1, fun _ => conv (evTr (ls.take k)), fun _ _ => (RA.step, sA, none)⟩

/-- The initial locations: the shared access's, then the private events'. -/
def locs1 (lsP : List Lab) (e : Ev) : List (Nat × Nat) :=
  (e.addr.toNat, e.n) :: (lsP.flatMap (·.evs)).map fun e => (e.addr.toNat, e.n)

theorem take_len_le {ls : List Lab} {P : Policy} {f : ArmState → ArmState}
    {ok : ArmState → Lab → Prop} {t t' : ArmState × Mon} (hr : PRun P f ok t ls t') (k : Nat) :
    ∀ j (h : j < (conv (evTr (ls.take k))).length), ((conv (evTr (ls.take k)))[j]).length ≤ 1 := by
  intro j hj
  have hj' : j < (evTr ls).length := by
    simp only [conv, evTr, List.length_map, List.length_take] at hj ⊢; omega
  have := prun_len hr j hj'
  simp only [conv, evTr, List.getElem_map, List.length_map, List.getElem_take] at this ⊢
  exact this

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then one shared
access `e`** (no `relXW` among them), its realized prefix covering the run (`Covers`): every
execution of the realized prefix with the initial locations `locs1` (the shared one first, the
CLIF one), reads from the latest earlier write (`wf_single`) and any initial memory is
`Realizes`d by a CLIF thread from `cs`. -/
theorem realizes_one_cov {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, Compiled env p RA cs sA) {lsP : List Lab} {e : Ev} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (lsP ++ [⟨[e], false⟩]) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (he : e.k ≠ .relXW) (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k ≤ lsP.length + 1, Covers env p RA cs (lsP ++ [⟨[e], false⟩]) k ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
      PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e) M0
        (latestW (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
        (coL (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e)) (fun _ _ => False)
        PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, hcv, hR⟩ := realizes_compiled_full (n := 1) (env := env) (p := p)
    (RA := fun _ => RA) (cs := fun _ => cs) (sA := fun _ => sA) (fun _ _ => hc env p)
    (mon := fun _ => none) (ls := fun _ => lsP ++ [⟨[e], false⟩]) (t' := fun _ => t')
    (fun _ _ => hr)
  -- the events of the run
  have hevs : ∀ l ∈ lsP ++ [⟨[e], false⟩], ∀ e' ∈ l.evs,
      e' = e ∨ (∃ q : Nat, ((lsP.flatMap (·.evs)).map fun e : Ev => (e.addr.toNat, e.n))[q]? =
        some (e'.addr.toNat, e'.n)) ∧ PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · refine .inr ⟨?_, hevP l hl e' he'⟩
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp
        (List.mem_map_of_mem (f := fun e : Ev => (e.addr.toNat, e.n))
          (List.mem_flatMap.mpr ⟨l, hl, he'⟩))
      exact ⟨q, hq⟩
    · simp only [List.mem_singleton] at hl
      subst hl
      exact .inl (List.mem_singleton.mp he')
  have hkind : ∀ l ∈ lsP ++ [⟨[e], false⟩], ∀ e' ∈ l.evs, e'.k ≠ .relXW := by
    intro l hl e' he'
    rcases hevs l hl e' he' with rfl | ⟨-, -, h | h⟩
    · exact he
    all_goals rw [h]; decide
  let P := PA1 RA sA (lsP ++ [⟨[e], false⟩]) (k 0)
  have hev : ∀ j kk x, P.evAt (.thr 0 j kk) = some x →
      ∃ l ∈ lsP ++ [⟨[e], false⟩], ∃ e' ∈ l.evs, x = ProgE2E.convEv e' := by
    intro j kk x hx
    simp only [Traces.evAt, P, PA1, show (0 : Nat) < 1 from by decide, ite_true] at hx
    obtain ⟨l, hl, e', he', rfl⟩ := evAt_conv_mem (p := (j, kk)) hx
    exact ⟨l, List.mem_of_mem_take hl, e', he', rfl⟩
  have hwf := wf_single (P := P) (locs := locs1 lsP e) rfl
    (take_len_le hr (k 0)) (fun r hr' => by
      cases r with
      | init q =>
        simp only [X0, Traces.exec] at hr'
        split at hr' <;> cases hr'
      | thr i j kk =>
        simp only [X0, Traces.exec] at hr' ⊢
        split at hr'
        · rename_i x hx
          have hi : i = 0 := by
            simp only [Traces.evAt, P, PA1] at hx
            split at hx
            · omega
            · cases hx
          subst hi
          obtain ⟨l, hl, e', he', rfl⟩ := hev j kk x hx
          rcases hevs l hl e' he' with rfl | ⟨⟨q, hq⟩, -⟩
          · refine ⟨.init 0, by simp [locs1], ?_, trivial⟩
            simp [hx, locs1, ProgE2E.convEv]
          · have hq' : q + 1 < (locs1 lsP e).length := by
              have := (List.getElem?_eq_some_iff.mp hq).1
              simp only [locs1, List.length_cons]; omega
            refine ⟨.init (q + 1), by simp only [hq', ite_true], ?_, trivial⟩
            simp only [hx, locs1, List.getElem?_cons_succ, hq, Option.getD_some, ProgE2E.convEv]
        · cases hr')
  obtain ⟨PC, φ, h1, h2, h3, h4⟩ := hR P (locs1 lsP e) [(e.addr.toNat, e.n)] M0 M0
    (latestW P (locs1 lsP e)) (coL P (locs1 lsP e)) (fun _ _ => False) rfl
    (fun i hi => by obtain rfl : i = 0 := by omega
                    rfl) hwf
    (fun i hi a b => by
      obtain rfl : i = 0 := by omega
      refine ⟨False.elim, fun ⟨_, ⟨y, hy, hyk⟩, _⟩ => ?_⟩
      obtain ⟨l, hl, hyl⟩ := evAt_evTr_mem hy
      exact hkind l (List.mem_of_mem_take hl) y hyl hyk)
    ⟨_, rfl⟩
    (fun q hq hq1 => by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by simp at hq1; omega⟩
      have hq2 : q' < ((lsP.flatMap (·.evs)).map fun e => (e.addr.toNat, e.n)).length := by
        simp only [locs1, List.length_cons] at hq; omega
      have hm := List.getElem_mem hq2
      obtain ⟨e', he', he'q⟩ := List.mem_map.mp hm
      obtain ⟨l, hl, he'l⟩ := List.mem_flatMap.mp he'
      refine ⟨0, by omega, ?_⟩
      simp only [locs1, List.getElem_cons_succ, ← he'q]
      exact (hevP l hl e' he'l).1)
    (fun q h => rfl) (fun i hi j hj hne => by omega)
  exact ⟨k 0, by have := hk 0 (by omega); simpa using this, hcv 0 (by omega), PC, φ, h1,
    h2 0 (by omega), h3, h4⟩

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then one shared
access `e`** (`realizes_one_cov` without the coverage). -/
theorem realizes_one {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, Compiled env p RA cs sA) {lsP : List Lab} {e : Ev} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (lsP ++ [⟨[e], false⟩]) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (he : e.k ≠ .relXW) (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k ≤ lsP.length + 1, ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
      PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e) M0
        (latestW (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
        (coL (PA1 RA sA (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e)) (fun _ _ => False)
        PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, -, h⟩ := realizes_one_cov hc hr hevP he env p M0
  exact ⟨k, hk, h⟩

/-- **A covering prefix of a private run ending in one shared access is the whole run** when the
CLIF thread cannot stop at its start and steps with a non-fence event: its first step's events
would be in the private part. -/
theorem one_full {env : Clif.Env} {p : Clif.Program} {RA : Backend.Proof.RL} {cs : Clif.State}
    {lsP : List Lab} {e : Ev} {k : Nat} (hcov : Covers env p RA cs (lsP ++ [⟨[e], false⟩]) k)
    (hk : k ≤ lsP.length + 1) (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat)
    (hgo : ¬ Stop env p (.run cs))
    (hone : ∀ evs t', CStep env p (.run cs) evs t' → ∃ i, ∃ hi : i < evs.length, evs[i].dir ≠ .F) :
    k = lsP.length + 1 := by
  have := covers_full hcov (by simpa using hk) hgo fun evs t' hs k' hk' ψ hsh _ => by
    obtain ⟨i, hi, hF⟩ := hone evs t' hs
    obtain ⟨hnp, y, hy, -, hl⟩ := hsh i hi hF
    obtain ⟨l, hl', e', he', rfl⟩ := evAt_conv_mem hy
    have hk'' : k' ≤ lsP.length := by simp at hk'; omega
    rw [List.take_append_of_le_length hk''] at hl'
    exact hnp (by rw [← hl]; exact hevP l (List.mem_of_mem_take hl') e' he')
  simpa using this

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then one shared
access, on the whole run** (`realizes_one_cov`, `one_full`): when the CLIF thread from `cs`
cannot stop at its start and steps with a non-fence event. -/
theorem realizes_one_full {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, Compiled env p RA cs sA) {lsP : List Lab} {e : Ev} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (lsP ++ [⟨[e], false⟩]) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (he : e.k ≠ .relXW) (env : Clif.Env) (p : Clif.Program) (M0 : Bytes)
    (hgo : ¬ Stop env p (.run cs))
    (hone : ∀ evs t', CStep env p (.run cs) evs t' → ∃ i, ∃ hi : i < evs.length, evs[i].dir ≠ .F) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
      PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (lsP ++ [⟨[e], false⟩]) (lsP.length + 1)) (locs1 lsP e) M0
        (latestW (PA1 RA sA (lsP ++ [⟨[e], false⟩]) (lsP.length + 1)) (locs1 lsP e))
        (coL (PA1 RA sA (lsP ++ [⟨[e], false⟩]) (lsP.length + 1)) (locs1 lsP e)) (fun _ _ => False)
        PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, hcv, h⟩ := realizes_one_cov hc hr hevP he env p M0
  obtain rfl := one_full hcv hk (fun l hl e' he' => (hevP l hl e' he').1) hgo hone
  exact h

/-! ## The run through the `ldar` -/

/-- The spill of `x0` to its slot and back. -/
def spillL : List (Loc × Loc) := [(.reg (.x 0), .stack 0 .int), (.stack 0 .int, .reg (.x 0))]

/-- The items after the spill moves. -/
def rest2L : List RItem := (rfL.blocks[0]!).toList.drop 21

/-- The kinds of a move's lines are plain (as a check). -/
def moveOkB (R : Backend.Proof.RL) (pK : AKind → Bool) (p : Loc × Loc) : Bool :=
  match R.fr.moveInsts p.1 p.2 with
  | .ok code => match codeLinesE R.ctx R.af code {} with
    | .ok (ls1, _) => (kinds ls1).all pK
    | .error _ => true
  | .error _ => true

/-- The code of the items after the spill moves starts with the `ldar` (as a check). -/
def headLdB : Bool :=
  match itemsCode RAL.fr vcpL.blocks[0]! rest2L with
  | .ok (.inst (.loadAcquire ty (.x 1) (.x 0) fl) :: _) =>
    ty.bits == 64 && (match fl.trapCode with | some .heapOob => true | _ => false)
  | _ => false

/-- The entry `args` (as a check). -/
def argsB : Bool :=
  match vcpL.blocks[0]? with
  | some vb => (match vb.insts[0]? with
    | some (MInst.args [(Reg.vreg 0 RegClass.int, Reg.x 0)]) => true
    | _ => false) && vb.insts.size == 3
  | none => false

theorem checksRunL : (rfL.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++
      (.op 0 #[.reg (.x 0)] :: (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L)) ∧
    savesL.all (moveOkB RAL (· == .plainW)) = true ∧
    spillL.all (moveOkB RAL fun K => K == .plainW || K == .plainR) = true ∧ headLdB = true ∧
    argsB = true ∧ 0 < vcpL.blocks.size := by
  native_decide

theorem moves_kinds {R : Backend.Proof.RL} {pK : AKind → Bool} {mvs : List (Loc × Loc)}
    (h : mvs.all (moveOkB R pK) = true) :
    ∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
      codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → ∀ K ∈ kinds ls1, pK K = true := by
  intro p hp code ls1 hc hl K hK
  have h := (List.all_eq_true.mp h) p hp
  simp only [moveOkB, hc, hl, List.all_eq_true] at h
  exact h K hK

theorem vb0L : RAL.vc.blocks[0]? = some vcpL.blocks[0]! := by
  show vcpL.blocks[0]? = _
  rw [Array.getElem?_eq_getElem checksRunL.2.2.2.2.2]
  simp [getElem!_def, Array.getElem?_eq_getElem checksRunL.2.2.2.2.2]

theorem argsL0 : (vcpL.blocks[0]!).insts[0]? = some (.args [(.vreg 0 .int, .x 0)]) ∧
    (vcpL.blocks[0]!).insts.size = 3 := by
  have h := checksRunL.2.2.2.2.1
  unfold argsB at h
  rw [show vcpL.blocks[0]? = some vcpL.blocks[0]! from vb0L] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  revert h1
  generalize (vcpL.blocks[0]!).insts[0]? = oi
  intro h1
  split at h1
  · rfl
  · cases h1

theorem head_ldarL : ∀ vb code, RAL.vc.blocks[0]? = some vb → itemsCode RAL.fr vb rest2L = .ok code →
    ∀ ps ls ps', codeLinesE RAL.ctx RAL.af code ps = .ok (ls, ps') →
      ls.head? = some (.ins (.ldar 64 (.x 1) (.x 0)) (some .heapOob)) := by
  intro vb code hvb hc ps ls ps' hl
  rw [vb0L] at hvb
  obtain rfl := (Option.some.inj hvb).symm
  have h := checksRunL.2.2.2.1
  simp only [headLdB, hc] at h
  split at h
  · rename_i ty fl rest e
    cases e
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hty, htc⟩ := h
    have hh := codeLinesE_head_ldar hl
    rw [hty] at hh
    rw [hh]
    revert htc
    cases fl.trapCode with
    | none => intro h; cases h
    | some c => cases c <;> intro h <;> first | rfl | cases h
  · cases h

/-- The entry `args` as a step of the allocated code (no code, the world unchanged; `x0`
in the store gets the world's `x0`). -/
theorem args_step (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RAL.vc RAL.sem ckeep RAL.rf (.run ⟨0, .op 0 #[.reg (.x 0)] :: its, m, w⟩)
      (.run ⟨0, its, m', w⟩) ∧ m' (.reg (.x 0)) = regVal w (.x 0) := by
  obtain ⟨hi, hsz⟩ := argsL0
  refine ⟨_, MStep.op vb0L hi (operands_args [(0, .x 0)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_⟩
  simp [writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

theorem regVal_x0 {s : ArmState} {v : CV} (h : v = regVal s (.x 0)) (hv : v = 0) :
    read_gpr 64 (BitVec.ofNat 5 0) s = 0 := by
  have := congrArg lo64 h
  rw [lo64_regVal_x, hv] at this
  simp only [read_gpr, BitVec.setWidth_eq]
  exact this.symm.trans (by simp [lo64])

/-- **The run of the compiled `atomic_load` through its `ldar`**: after the prologue, a precise
run reading the thread's own bytes whose last step is the `ldar`'s single event (`acqR`, 8 bytes
at address 0, the argument), every earlier event private and plain; `Compiled` at its start. -/
theorem run_load : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    (∀ env p, Compiled env p RAL csL (iterN RAL.step n RAL.s0)) ∧
    PRun Policy.arm RAL.step (OkPriv RAL) (iterN RAL.step n RAL.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .acqR ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨n', hq, hA⟩ := qRL
  have e0 := checksRunL.1
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show RAL.rf = rfL from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRL (fun K => (K == .plainW) = true)
    savesL _ _ _ none hq0 hA0 (moves_kinds checksRunL.2.1) (by simp [savesL, Loc.isSave])
  -- the entry `args`
  obtain ⟨m', hst, hm'⟩ := args_step (spillL.map (fun p => RItem.move p.1 p.2) ++ rest2L) _ w₀L
  have hq2 := realizes_args wfRL hq1 hA1 vb0L argsL0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRL hq1 hA1 hst
  -- the spill moves
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRL
    (fun K => (K == .plainW || K == .plainR) = true) spillL rest2L t1.1 m' t1.2 hq2 hA2
    (moves_kinds checksRunL.2.2.1) (by simp [spillL, Loc.isSave])
  -- the `ldar`
  obtain ⟨j, hj, hpc, hstr⟩ := q_head wfRL hq3 rfl (fun _ h => by cases h) head_ldarL
  obtain ⟨t3, ev, r3, -, hk, hn, ha⟩ := excl_step_fwd wfRL hj rfl hstr.prog hpc hstr.err
    (lb := 1) (p := 1) (q := 0) (.inr rfl) (by omega) (by omega) (fun _ => rfl) t2.2
  simp only [ite_true] at hk
  -- its address: the argument, `x0 = 0`
  have hx0 : movesM spillL m' (.reg (.x 0)) = regVal w₀L (.x 0) := by
    simp [movesM, spillL, Backend.Proof.upd, hm']
  have hs3 := hstr.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
  rw [hx0] at hs3
  have hz : regVal w₀L (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeL.2.2.2.2.2.2.2]
  have hr : PRun Policy.arm RAL.step (OkPriv RAL) (iterN RAL.step n' RAL.s0, none)
      ((ls1 ++ ls2) ++ [⟨[ev], false⟩]) t3 := PRun.append (PRun.append r1 r2) r3
  have hevP : ∀ l ∈ ls1 ++ ls2, ∀ e' ∈ l.evs,
      PrivA RAL e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
      exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
    · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
      exact ⟨privA_addr.2 hF, by simpa using hK⟩
  exact ⟨n', ls1 ++ ls2, ev, t3, fun env p => compiled_ofL hq hA env p, hr, hk, hn,
    ha.trans (regVal_x0 hs3 hz), hevP⟩

/-- **`Realizes` on the compiled `atomic_load` through its `ldar`** (module doc): the run of
`run_load`; every execution of its realized prefix (initial locations `locs1`, the `ldar`'s
first) is `Realizes`d by a CLIF thread from `csL`. -/
theorem realizes_load : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAL.step (OkPriv RAL) (iterN RAL.step n RAL.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .acqR ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k ≤ lsP.length + 1,
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csL ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e) M0
          (latestW (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
          (coL (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
          (fun _ _ => False) PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, e, t', hc, hr, hk, hn, ha, hevP⟩ := run_load
  exact ⟨n, lsP, e, t', hr, hk, hn, ha, hevP, fun env p M0 =>
    realizes_one hc hr hevP (by rw [hk]; decide) env p M0⟩

/-! ## The whole run -/

theorem bodyL : ∃ st rest, csL.frame.body = st :: rest ∧ st.inst = .atomicLoad .i64 {} 0 := by
  have h : csL.frame.body.head?.map (·.inst) = some (.atomicLoad .i64 {} 0) := by native_decide
  revert h
  cases csL.frame.body with
  | nil => intro h; cases h
  | cons st rest => intro h; exact ⟨st, rest, rfl, by simpa using h⟩

theorem regL0 : csL.frame.regs 0 = some ⟨.i64, 0⟩ := by native_decide

theorem stepL0 : (match Clif.step default default (withBytes csL (fun _ => some 0)) with
    | .next _ => true | _ => false) = true := by native_decide

/-- **The CLIF thread from `csL` steps** (its `atomic_load`, on bytes `0`). -/
theorem cstep_csL (env : Clif.Env) (p : Clif.Program) : ∃ evs t', CStep env p (.run csL) evs t' := by
  obtain ⟨st, rest, hb, hi⟩ := bodyL
  have hb' : (withBytes csL (fun _ => some 0)).frame.body = st :: rest := hb
  obtain ⟨s', hs⟩ := step_next_of_check (env := env) (p := p) hb'
    (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h) default
    default stepL0
  exact ⟨_, _, ClifCStep.cstep_atomicLoad hb' hi regL0 hs⟩

theorem shapeL1 : evShape csL = [[(.scR, 8)]] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyL
  simp only [evShape, hb, hi]
  rfl

theorem notStop_csL (env : Clif.Env) (p : Clif.Program) : ¬ Stop env p (.run csL) := by
  obtain ⟨st, rest, hb, hi⟩ := bodyL
  obtain ⟨evs, t', hs⟩ := cstep_csL env p
  rintro (hd | hc)
  · exact hd ⟨evs, t', hs⟩
  · exact not_casRO hb (fun _ _ _ _ _ h => by rw [hi] at h; cases h) hc

/-- **`Realizes` on the compiled `atomic_load` through its `ldar`, on the whole run** (T2j): the
run of `run_load`; every execution of all of it is `Realizes`d by a CLIF thread from `csL`
(`realizes_one_full`: the CLIF thread steps from `csL`, with the `atomic_load`'s read). -/
theorem realizes_load_full : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAL.step (OkPriv RAL) (iterN RAL.step n RAL.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .acqR ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes),
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csL ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
          (locs1 lsP e) M0
          (latestW (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
            (locs1 lsP e))
          (coL (PA1 RAL (iterN RAL.step n RAL.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
            (locs1 lsP e))
          (fun _ _ => False) PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, e, t', hc, hr, hk, hn, ha, hevP⟩ := run_load
  exact ⟨n, lsP, e, t', hr, hk, hn, ha, hevP, fun env p M0 =>
    realizes_one_full hc hr hevP (by rw [hk]; decide) env p M0 (notStop_csL env p)
      (fun _ _ hs => nonFence_one shapeL1 (by decide) hs)⟩

end Concurrency.RealizeCompiled.WitnessL
