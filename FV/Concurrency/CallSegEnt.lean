import FV.Concurrency.CallSegOkG
import FV.Concurrency.CallEntryRel

/-!
# The callee's activation at a caller's call (#473, `SegOkG` call case, item (1))

At a caller's paused `call` (the chain theorem's call end), the `bl` enters the callee `FB` and
the CLIF call enters the callee function `fB` (`CallStepT.realizedT_call`'s entry state `cs`).
**`callee_chainP`**: given the callee's `FnOk`, its activation `h` (entered at
`enter FB x`, budget `KB`, kept addresses the caller's frame and kept addresses, its slots placed
by the oracle, the memory relation of its world) has its `StatOk` and its chain property from its
ABI entry with CLIF state `cs` (`chainP_entry`): the entry memory relation from
`CallEntryRel.callee_relW`, the arguments, `Q` and `AInv` from `CallSegCall.call_endK`.
-/

namespace Concurrency.CallSegEnt

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link CallSegOkG CallSegCall CallEntryRel FrameDisj ArmFoot
  ArmInstFoot

/-- **The callee's activation and its chain property** (module doc). (#581: `hpB`, the callee's
stack probes below its frame within its budget `KB`, is new: the callee's `R.Wf` includes
`StackAvail`, which now bounds them.) -/
theorem callee_chainP {L : Link} {env : Clif.Env} {p : Clif.Program}
    {syms : String → Option Nat} {g : Act} (hS : StatOk L env p g) (hsyms : g.Γ.syms = syms)
    (hcin : CodeIn L (g.RL L)) {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState}
    {cM' : MState CV ArmState} (hq : Q (g.RL L) x (.run cM')) (hP : Pause (g.RL L) (.run cM'))
    (hm2 : Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s' vV')
    (hm3 : PMatch g.vc g.F.vc (csem (g.RL L).F (g.RL L).ctx (g.RL L).X)
      (cEvs (g.RL L).F (g.RL L).ctx) g.Lp g.ss' (.run vV') (.run vP'))
    (hm4 : MatchRun g.cc g.ins ckeep (g.r0 L) cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {e : Clif.ExtFunc} (he : s'.frame.func.extern? fn = some e)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys e.sig.params)
    {FB : LFn} (hB : (e.name, FB) ∈ L.fns) {fB : Clif.Function} (hsig : fB.sig = e.sig)
    (hFn : FnOk L env p syms e.name FB fB) {KB : Nat} (hKB : FB.af.frameSize + 16 + KB ≤ g.K)
    (hpB : probeBelow FB.af ≤ KB)
    {sps : List (BitVec 64)} {fr : String → Option (Nat × (Clif.SlotId → Nat))}
    (hpl : s'.mem.place = some ⟨spv x :: sps, fr, none⟩)
    (hfr : fr fB.name = some (frameDrop FB.af, slotOffs FB.af fB))
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : fB.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = fB)
    (hslots : cs.frame.slots = (Clif.enterSlots fB s'.mem).1)
    (hmem : cs.mem = (Clif.enterSlots fB s'.mem).2) (hbodyc : cs.frame.body = B0.body)
    (htermc : cs.frame.term = B0.term)
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some cs.frame.regs)
    (hty : vals.map (·.ty) = B0.params.map (·.2))
    (hsigc : vals.map (·.ty) = fB.sig.params.map (·.ty))
    (ext : List (Clif.Frame × List Clif.ValueId)) (caller : LFn) (opens : List (Clif.Mem × Nat))
    (N : Nat → Prop) (sps : List (BitVec 64)) :
    ∃ h : Act, h.nm = e.name ∧ h.F = FB ∧ h.s0 = enter FB x ∧ h.K = KB ∧
      h.G = (g.RL L).FK ∧ h.ra = Arm.r .PC x + 4#64 ∧ h.f = fB ∧
      h.slots = (Clif.enterSlots fB s'.mem).1 ∧ h.ext = ext ∧ h.caller = caller ∧
      h.opens = opens ∧ h.N = N ∧ h.sps = sps ∧ h.Γ.syms = syms ∧ StatOk L env p h ∧
      (∀ mon, ChainP L env p h (h.r0 L) (h.s0, mon) cs) ∧ CodeIn L (h.RL L) ∧
      Nested (g.RL L) (h.RL L) ∧ L.M x = enter FB x ∧ stepEvs x = [] ∧ cls x = .plain ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (enter FB x) = Arm.r f x) ∧
      xreg 30 (enter FB x) = Arm.r .PC x + 4#64 := by
  have huniq : ∀ e' ∈ g.f.externs, e'.2.name = e.name → e'.2 = e :=
    fun e' he' hn => hS.uniq e' he' _ (CallSegOkG.mem_of_lookup (hm2.2.1 ▸ he)) hn
  obtain ⟨hM, hev, hcls, hWf, habi, hfx, hlr, -, hQ, hAI, hargs, hcinB, hnest⟩ :=
    call_endK hS.ok hS.mem hS.wf hcin hS.H hS.chk hS.res hS.cu hS.low hS.ind hS.ver hS.nt hS.out0
      hS.slot hS.sym hS.noCall hS.H3 hS.checked hS.uv hS.dv hq hP hm2 hm3 hm4 hbody hcl he huniq
      hvals htys hB hFn.1 hKB hpB hsig
  obtain ⟨wA, hmr, hmx, herr, -⟩ := caller_world hS.noCall hS.H hS.chk hS.H3 hS.checked hq hP
    ⟨stm, rest, fn, args, hbody, hcl⟩ hm2 hm3 hm4
  rw [hS.ΓF, hsyms] at hmr
  have hrel := callee_relW hS.wf hcin hB hWf hnest hmr hmx herr hpl hfr hFn.2.2.1
  -- the callee's body-entry `sp` is 16-aligned
  have hal : (spv (bodyOf FB.af (enter FB x))).toNat % 16 = 0 := by
    have hx : (spv x).toNat % 16 = 0 := (checkSP_iff x).mp (q_stRel hq).align
    have hfs : FB.af.frameSize % 16 = 0 := hFn.2.1
    have hle : frameDrop FB.af ≤ (spv x).toNat := by
      obtain ⟨-, h2⟩ := spB_toNat hWf
      have : (spv (enter FB x)).toNat = (spv x).toNat := by rw [CallEntryRel.spv_enter]
      simp only [act_af, act_s0] at h2; omega
    have hlt := (spv x).isLt
    have hd : frameDrop FB.af < 2 ^ 64 := by omega
    have e : (spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat = (spv x).toNat - frameDrop FB.af := by
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; exact hle),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    rw [spv_bodyOf, CallEntryRel.spv_enter, e]
    unfold frameDrop at hle ⊢
    by_cases hf : FB.af.frame = true
    · simp only [hf, ite_true] at hle ⊢; omega
    · simp only [Bool.not_eq_true] at hf
      simp only [hf, Bool.false_eq_true, ite_false] at hle ⊢; omega
  obtain ⟨-, -, -, vc, ctx, st0, R, gn, bl, A, Lp, ss, ss', cc, ins, a0, hst⟩ := hFn
  have hSB := hst (enter FB x) KB (g.RL L).FK (Arm.r .PC x + 4#64)
    (spv (bodyOf FB.af (enter FB x))) (Clif.enterSlots fB s'.mem).1 ext caller opens N sps hWf habi
    hal
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hSB,
    fun mon => ?_, hcinB, hnest, hM, hev, hcls, hfx, hlr⟩
  exact chainP_entry hSB hB0 hcall hfunc (by rw [hslots]) hbodyc htermc hregs hty
    (by rw [hsigc]) (by rw [hmem]; exact hrel) hargs hQ hAI

end Concurrency.CallSegEnt
