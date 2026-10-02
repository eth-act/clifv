import FV.E2E.LinkArm

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

def src : String := "function %h(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = iadd v0, v1
    return v2
}

function %g(i64) -> i64 {
    fn0 = colocated %h(i64) -> i64
block0(v0: i64):
    v1 = call fn0(v0)
    v2 = iadd v1, v0
    return v2
}

function %f(i64) -> i64 {
    fn0 = colocated %g(i64) -> i64
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def raOut : String := "{\"functions\":[{\"allocs\":[[\"x0\"],[\"x2\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"h\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\",\"x19\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x19\"}],\"name\":\"g\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"f\",\"num_spillslots\":0,\"ok\":true}]}"

deriving instance Inhabited for Art

def getOk {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => default

theorem getOk_eq {ε α : Type} [Inhabited α] {x : Except ε α} (h : x.toBool = true) :
    x = .ok (getOk x) := by
  cases x <;> simp_all [getOk, Except.toBool]

def fn (i : Nat) : Clif.Function := match (Clif.parseFile src).funcs[i]? with
  | some p => getOk p.func
  | none => default

def fH : Clif.Function := fn 0
def fG : Clif.Function := fn 1
def fF : Clif.Function := fn 2

def raJ (i : Nat) : Lean.Json :=
  (((getOk (Lean.Json.parse raOut)).getObjVal? "functions").bind (·.getArr?)).toOption.getD #[] |>.getD i default

/-- The pipeline on function `i` of `src` with index `k` and load address `base`. -/
def pipe (f : Clif.Function) (k : Nat) (base : BitVec 64) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare vc
  let o ← parseRAOut (raJ k)
  let rf ← buildRFunc vcp o
  let af ← lowerRFunc vcp rf
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, rf, af, fa, fb, base⟩


/-! ## The program and its compiled image -/

/-- The program `{f, g, h}`. -/
def P : Clif.Program := { funcs := [fF, fG, fH] }

/-- The file index of a function of `P` (the regalloc2 output and the local labels). -/
def idx (g : Clif.Function) : Nat := if g = fF then 2 else if g = fG then 1 else 0

/-- The load address of a function of `P`. -/
def baseOf (g : Clif.Function) : BitVec 64 := 0x10000 * BitVec.ofNat 64 (idx g + 1)

/-- The compiled image of every function. -/
def A (g : Clif.Function) : Art := getOk (pipe g (idx g) (baseOf g))

theorem pipe_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {a : Art}
    (h : pipe f k base = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipe at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : parseRAOut (raJ k) with _ | o <;> simp only [h3] at h
  · cases h
  rcases h4 : buildRFunc vcp o with _ | rf <;> simp only [h4] at h
  · cases h
  rcases h5 : lowerRFunc vcp rf with _ | af <;> simp only [h5] at h
  · cases h
  rcases h6 : emitFunc k af with _ | fa <;> simp only [h6] at h
  · cases h
  rcases h7 : fa.layout with _ | fb <;> simp only [h7] at h
  · cases h
  cases h
  exact ⟨rfl, h2, h5, h6, h7, rfl, rfl⟩

/-! ## Executable checks of the premises -/

/-- Every instruction of `vc` satisfies `p`. -/
def allInsts (vc : VCode) (p : MInst → Bool) : Bool := vc.blocks.all fun vb => vb.insts.all p

theorem allInsts_sound {vc : VCode} {p : MInst → Bool} (h : allInsts vc p = true) {b k : Nat}
    {vb : VBlock} {i : MInst} (hb : vc.blocks[b]? = some vb) (hk : vb.insts[k]? = some i) :
    p i = true :=
  (array_all_iff _ _).1 ((array_all_iff _ _).1 h b vb hb) k i hk

/-- `q` at every call site. -/
def siteB (q : CallInfo → Bool) : MInst → Bool
  | .call info => q info
  | .tryCall info _ => q info
  | _ => true

theorem site_sound {vc : VCode} {q : CallInfo → Bool} (h : allInsts vc (siteB q) = true)
    {info : CallInfo} (hs : vc.CallSite info) : q info = true := by
  obtain ⟨b, vb, k, hb, hk | ⟨ti, hk⟩⟩ := hs
  · simpa [siteB] using allInsts_sound h hb hk
  · simpa [siteB] using allInsts_sound h hb hk

def decU (us : List (Reg × Reg)) : List (Nat × Reg) :=
  us.map fun p => ((match p.1 with | .vreg n _ => n | _ => 0), p.2)

def decD (ds : List (Reg × Reg)) : List (Reg × Nat) :=
  ds.map fun p => (p.1, match p.2 with | .vreg n _ => n | _ => 0)

/-- A call site: a `bl` of a function `h` of `P`, arguments in `h`'s parameter registers, results
from x0... -/
def siteOk (P : Clif.Program) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => decide (h ≠ g) && decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide ((decD info.defs).map (·.1) = (List.range (sigRets h.sig).length).map Reg.x)
    | none => false
  | .reg _ => false

theorem siteOk_sound {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOk P g info = true) :
    ∃ n h', info.dest = .sym n ∧ P.func? n = some h' ∧ h' ≠ g ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      Ld.map (·.1) = (List.range (sigRets h'.sig).length).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => simp at h
  | sym n =>
    cases hf : P.func? n with
    | none => simp [hf] at h
    | some h' =>
      simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hne, hu⟩, hd⟩, h1⟩, h2⟩ := h
      exact ⟨n, h', rfl, hf, hne, _, _, by rw [← hu, ← hd], h1, h2⟩

def isRegLoc : ArgLoc → Bool
  | .reg _ => true
  | .stack _ => false

/-- The entry `Args` reads parameter registers. -/
def entryB (g : Clif.Function) (vc : VCode) : Bool :=
  match vc.blocks[0]? with
  | some vb => match vb.insts[0]? with
    | some (MInst.args ds) => ds.all fun p => decide (p.2 ∈ regLocs g.sig)
    | _ => true
  | none => true

theorem entryB_sound {g : Clif.Function} {vc : VCode} (h : entryB g vc = true) {r : Reg}
    (hr : vc.EntryArg r) : r ∈ regLocs g.sig := by
  obtain ⟨vb, ds, hb, hi, v, hv⟩ := hr
  simp only [entryB, hb, hi, List.all_eq_true, decide_eq_true_eq] at h
  exact h _ hv

/-- No `call_indirect`, `try_call_indirect`, `return_call`. -/
def linkFreeB (g : Clif.Function) : Bool :=
  g.blocks.all fun b =>
    b.body.all (fun st => match st.inst with | .callIndirect .. => false | _ => true) &&
    (match b.term with | .tryCallIndirect .. => false | .returnCall .. => false | _ => true)

theorem linkFreeB_sound {g : Clif.Function} (h : linkFreeB g = true) : Clif.LinkFree g := by
  intro b hb
  simp only [linkFreeB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨fun st hst sig callee args he => ?_, fun callee args et he => ?_, fun fn args he => ?_⟩
  · have := h1 st hst; rw [he] at this; simp at this
  · rw [he] at h2; simp at h2
  · rw [he] at h2; simp at h2

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → b ∈ l.map (·.2)
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- The call instructions of the laid-out code. -/
def callLine : Line → Bool
  | .ins (.bl _) _ => true
  | .ins (.blr _) _ => true
  | _ => false

/-- The return address of every call of `a` (the code of `g`) is outside the code of every other
function of `P`. -/
def raCallB (P : Clif.Program) (A : Clif.Function → Art) (g : Clif.Function) (a : Art) : Bool :=
  let ls := a.fa.lines.toList
  (List.range ls.length).all fun j =>
    match ls[j]? with
    | some l => !callLine l || P.funcs.all fun h => decide (h = g) || let ah := A h
        (List.range ah.fb.words.size).all fun k =>
          a.base + BitVec.ofNat 64 (lineOffset ls j) + 4 != ah.base + BitVec.ofNat 64 (4 * k)
    | none => true

theorem raCallB_sound {P : Clif.Program} {A : Clif.Function → Art} {g : Clif.Function} {a : Art}
    (h : raCallB P A g a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) :
    ∀ h' ∈ P.funcs, h' ≠ g → ∀ k < (A h').fb.words.size, pc + 4 ≠ (A h').base + BitVec.ofNat 64 (4 * k) := by
  obtain ⟨j, i, t, hj, hi, rfl⟩ := hpc
  intro h' hh hne k hk
  have hjl : j < a.fa.lines.toList.length := (List.getElem?_eq_some_iff.1 hj).1
  simp only [raCallB, List.all_eq_true, List.mem_range] at h
  have := h j hjl
  rw [hj] at this
  have hc : callLine (.ins i t) = true := by
    rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range, bne_iff_ne,
    Bool.or_eq_true, decide_eq_true_eq] at this
  exact (this h' hh).resolve_left hne k hk

def raStarB (P : Clif.Program) (A : Clif.Function → Art) (ra : BitVec 64) : Bool :=
  P.funcs.all fun h => let ah := A h
    (List.range ah.fb.words.size).all fun k => ra != ah.base + BitVec.ofNat 64 (4 * k)

/-! ## The code image -/

/-- The words of every function at its base. -/
def progAll (P : Clif.Program) (A : Clif.Function → Art) : Arm.Program :=
  P.funcs.flatMap fun g => (A g).fb.program (A g).base

/-- The bytes of a list of code words. -/
def memOf (prog : Arm.Program) : Arm.Memory := fun a =>
  match List.find? (fun (p : BitVec 64 × BitVec 32) => decide ((a - p.1).toNat < 4)) prog with
  | some p => p.2.extractLsb' (8 * (a - p.1).toNat) 8
  | none => 0

/-- The code addresses of the functions of `P`. -/
def Img (P : Clif.Program) (A : Clif.Function → Art) (a : BitVec 64) : Prop :=
  ∃ g ∈ P.funcs, CodeAddr (Arm.set_program Arm.ArmState.default ((A g).fb.program (A g).base)) a

/-- The image read back word by word. -/
def imgB (P : Clif.Program) (A : Clif.Function → Art) : Bool :=
  P.funcs.all fun g => let a := A g
    (List.range a.fb.words.size).all fun k =>
      Arm.read_mem_bytes 4 (a.base + BitVec.ofNat 64 (4 * k))
        (setMem Arm.ArmState.default (memOf (progAll P A))) == a.fb.words[k]!

/-- The per-function checks. -/
def chk (g : Clif.Function) : Bool :=
  let a := A g
  (pipe g (idx g) (baseOf g)).toBool && (lowerCheck g a.vc && (prepCheck a.vc a.vcp &&
  ((checkAlloc a.vcp a.rf).toBool && (formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp &&
  (g.blocks.all (fun B => !B.term.isTry) && ((RAFrame.compute a.vcp a.rf).intBase == 0 &&
  ((locsOf g.sig).all isRegLoc && (decide (regLocs g.sig).Nodup &&
  ((regLocs g.sig).all (·.isArgReg) && (g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) &&
  ((g.sig.params.any (·.purpose == .sret) == false) && (decide (g.slots = []) &&
  ((RAFrame.compute a.vcp a.rf).size == a.af.frameSize && (allInsts a.vcp (siteB (siteOk P g)) &&
  (g.externs.all (fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => false) &&
  (entryB g a.vcp && (decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64) &&
  (raCallB P A g a && (decide (frameDrop a.af ≤ 32) && (!hasTls g && (linkFreeB g &&
  (Compile.functionE g && (g.externs.all (fun e => e.2.name != g.name) &&
  ((sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) &&
  (indSigs g).isEmpty))))))))))))))))))))))))

/-- All the executable checks. -/
def okB : Bool :=
  decide (P.funcs.map (·.name)).Nodup && (P.funcs.all chk && (imgB P A && raStarB P A 8))

theorem okB_true : okB = true := by native_decide

/-! ## Soundness of the image check -/

theorem wordsAt_mem {base : BitVec 64} {w : BitVec 32} :
    ∀ {ws : List (BitVec 32)} {k j : Nat}, ws[j]? = some w →
      List.Mem (base + BitVec.ofNat 64 (4 * (k + j)), w) (wordsAt base k ws)
  | [], _, _, h => by simp at h
  | x :: ws, k, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact .head _
  | x :: ws, k, j + 1, h => by
    apply List.Mem.tail
    have := wordsAt_mem (base := base) (ws := ws) (k := k + 1) (j := j) (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem rmb_congr {t t' : Arm.ArmState} : ∀ (n : Nat) (x : BitVec 64),
    (∀ i < n, t.mem (x + BitVec.ofNat 64 i) = t'.mem (x + BitVec.ofNat 64 i)) →
    Arm.read_mem_bytes n x t = Arm.read_mem_bytes n x t'
  | 0, _, _ => rfl
  | n + 1, x, h => by
    have h0 : t.mem x = t'.mem x := by simpa using h 0 (by omega)
    have ih := rmb_congr (t := t) (t' := t') n (x + 1#64) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega] at this
    simp only [Arm.read_mem_bytes, Arm.read_mem, Arm.read_store, ih, h0]

theorem imgCode_of {P : Clif.Program} {A : Clif.Function → Art} (h : imgB P A = true)
    {g : Clif.Function} (hg : g ∈ P.funcs) (t : Arm.ArmState)
    (ht : ∀ a, Img P A a → t.mem a = memOf (progAll P A) a) (k : Nat) (w : BitVec 32)
    (hw : (A g).fb.words[k]? = some w) :
    Arm.read_mem_bytes 4 ((A g).base + BitVec.ofNat 64 (4 * k)) t = w := by
  have hk : k < (A g).fb.words.size := (Array.getElem?_eq_some_iff.1 hw).1
  have hc := List.all_eq_true.1 (List.all_eq_true.1 h g hg) k (List.mem_range.2 hk)
  simp only [beq_iff_eq] at hc
  rw [show (A g).fb.words[k]! = w by simp [Array.getElem!_eq_getD, hw]] at hc
  rw [← hc]
  refine rmb_congr 4 _ fun i hi => ?_
  have hm := wordsAt_mem (base := (A g).base) (k := 0) (j := k) (ws := (A g).fb.words.toList)
    (by simpa using hw)
  rw [Nat.zero_add] at hm
  refine ht _ ⟨g, hg, ⟨_, hm, ?_⟩⟩
  rw [BitVec.add_comm _ (BitVec.ofNat 64 i), BitVec.add_sub_cancel]
  simp only [BitVec.toNat_ofNat]
  omega

/-! ## The facts the checks give -/

/-- What `chk g` says of `g`. -/
structure Facts (g : Clif.Function) : Prop where
  pipe : pipe g (idx g) (baseOf g) = .ok (A g)
  lowerOk : lowerCheck g (A g).vc = true
  prepOk : prepCheck (A g).vc (A g).vcp = true
  check : checkAlloc (A g).vcp (A g).rf = .ok ()
  covered : FormsCovered ⟨(A g).fa.k, (A g).af.slotBase⟩ (A g).vcp
  noTry : ∀ B ∈ g.blocks, B.term.isTry = false
  noOut : (RAFrame.compute (A g).vcp (A g).rf).intBase = 0
  regParams : ∀ l ∈ locsOf g.sig, ∃ r, l = .reg r
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  noSret : g.sig.params.any (·.purpose == .sret) = false
  slots : g.slots = []
  size : (RAFrame.compute (A g).vcp (A g).rf).size = (A g).af.frameSize
  sites : allInsts (A g).vcp (siteB (siteOk P g)) = true
  externs : ∀ e ∈ g.externs.map (·.2), ∃ h, P.func? e.name = some h ∧ e.sig = h.sig
  entry : entryB g (A g).vcp = true
  fits : (A g).base.toNat + 4 * (A g).fb.words.size ≤ 2 ^ 64
  ra : raCallB P A g (A g) = true
  depth : frameDrop (A g).af ≤ 32
  tls : hasTls g = false
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  extName : ∀ e ∈ g.externs.map (·.2), e.name ≠ g.name
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  ind : indSigs g = []

theorem toBool_unit {ε : Type} {x : Except ε Unit} (h : x.toBool = true) : x = .ok () := by
  cases x <;> simp_all [Except.toBool]

theorem chk_sound {g : Clif.Function} (h : chk g = true) : Facts g := by
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, ⟨h25, h25'⟩, h26⟩ := h
  refine ⟨getOk_eq h1, h2, h3, toBool_unit h4, (formsCoveredB_iff _ _).1 h5, h6, h7,
    fun l hl => ?_, h9, h10, h11, h12, h13, h14, h15, fun e he => ?_, h17, h18, h19, h20, h21,
    linkFreeB_sound h22, h23, fun e he => ?_, ⟨h25, h25'⟩, List.isEmpty_iff.1 h26⟩
  · have := h8 l hl
    cases l with
    | reg r => exact ⟨r, rfl⟩
    | stack _ => simp [isRegLoc] at this
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    have := h16 _ hm
    revert this
    cases hf : P.func? e'.name with
    | none => simp
    | some h => simp only [decide_eq_true_eq]; exact fun hs => ⟨h, rfl, hs⟩
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    simpa using h24 _ hm

theorem facts {g : Clif.Function} (hg : g ∈ P.funcs) : Facts g := by
  have := okB_true
  simp only [okB, Bool.and_eq_true, List.all_eq_true] at this
  exact chk_sound (this.2.1 g hg)

/-! ## The linked program -/

/-- The base environment's machine semantics: no extern outside `P` (`call` undefined), the
symbols at the functions' bases. -/
def Xb : ExtSem where
  call _ _ _ := none
  sym n _ := if n = "f" then 0x30000 else if n = "g" then 0x20000 else if n = "h" then 0x10000 else 0
  tp := 0
  tlsFlags _ s := Arm.read_pstate s

/-- The base hooks: a call outside `P` continues at the next instruction; TLS keeps the state. -/
def Hb : ArmHooks := ⟨fun _ s => Arm.w .PC (Arm.r .PC s + 4) s, fun _ _ s => s⟩

/-- **The linked program** `{f, g, h}` with the addresses `F` outside the world. -/
def L (F : BitVec 64 → Prop) : LinkSys where
  P := P
  A := A
  base := Clif.Env.empty
  Xb := Xb
  Hb := Hb
  syms := fun _ => none
  F := F
  Img := Img P A
  imgMem := memOf (progAll P A)
  raStar := 8
  D := 32

theorem names : fF.name = "f" ∧ fG.name = "g" ∧ fH.name = "h" := by native_decide

theorem mem_P {g : Clif.Function} : g ∈ P.funcs ↔ g = fF ∨ g = fG ∨ g = fH := by
  simp [P]

theorem symInj {h : Clif.Function} (hh : h ∈ P.funcs) (n : String)
    (hn : Xb.sym h.name 0 = Xb.sym n 0) : n = h.name := by
  obtain ⟨n1, n2, n3⟩ := names
  rcases mem_P.1 hh with rfl | rfl | rfl <;>
    simp only [Xb, n1, n2, n3] at hn ⊢ <;>
    by_cases e1 : n = "f" <;> by_cases e2 : n = "g" <;> by_cases e3 : n = "h" <;>
    simp_all (config := { decide := true })

/-- **`L.Ok`**: every premise of the linked program, for every `F` containing the code. -/
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (L F).Ok := by
  have hok := okB_true
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnames, -, himg, hstar⟩ := hok
  have site : ∀ g ∈ P.funcs, ∀ info h, (L F).ProgSite g info h →
      h ∈ P.funcs ∧ h ≠ g ∧ ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        Ld.map (·.1) = (List.range (sigRets h.sig).length).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    obtain ⟨n', h', hd', hf', hne, Lu, Ld, he, h1, h2⟩ := siteOk_sound (site_sound (facts hg).sites hs)
    rw [hd] at hd'; cases hd'
    have : h' = h := by simp only [L] at hf; rw [hf] at hf'; cases hf'; rfl
    subst this
    exact ⟨(Clif.Program.func?_some hf').1, hne, n, Lu, Ld, he, h1, h2⟩
  refine
    { linkable := ⟨hnames, fun g hg => (facts hg).free⟩
      subset := fun g hg => ⟨?_, (facts hg).subsetE, ?_, ?_, (facts hg).abi, ?_⟩
      compiled := fun g hg => ?_
      covered := fun g hg => (facts hg).covered
      noTry := fun g hg => (facts hg).noTry
      noOut := fun g hg => (facts hg).noOut
      regParams := fun g hg => (facts hg).regParams
      argRegs := fun g hg => ⟨(facts hg).nodup, (facts hg).argReg, (facts hg).width⟩
      noSret := fun g hg => (facts hg).noSret
      calleeSlots := fun g hg h hh => ?_
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2
      noBlr := fun g hg info hs => ?_
      symInj := fun h hh n hn => symInj hh n hn
      declSig := fun g hg e he h hf => ?_
      entryRegs := fun g hg r hr => entryB_sound (facts hg).entry hr
      fits := fun g hg => (facts hg).fits
      imgAddr := fun g hg a ha => ⟨g, hg, ha⟩
      imgCode := fun g hg t ht k w hw => imgCode_of himg hg t ht k w hw
      imgF := hF
      raCall := fun g hg info h hs pc hpc => ?_
      raStar := fun h hh k hk => ?_
      depth := fun g hg => (facts hg).depth
      symOk := fun n b hn => by simp [L] at hn
      baseOs := fun g hg info hs hb => ?_
      basePc := fun d s _ _ _ => by simp [L, Hb, Arm.r_of_w_same]
      baseExt := fun d uses w outs w' _ hx => by simp [L, Xb] at hx
      baseX := fun g hg F' slotOff out c => ?_
      baseTls := fun g hg ht => absurd ht (by simp [L, (facts hg).tls]) }
  · simp [L, Clif.Program.only, Clif.Program.func?]
  · intro b _ st _ fn args _ e he
    have hne := (facts hg).extName e (lookup_mem he)
    simp [L, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · intro b _ fn args et _ e he
    have hne := (facts hg).extName e (lookup_mem he)
    simp [L, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · rw [(facts hg).ind]; simp
  · obtain ⟨hl, hp, ha, he, hla, -, -⟩ := pipe_spec (facts hg).pipe
    exact ⟨hl, (facts hg).lowerOk, hp, (facts hg).prepOk, (facts hg).check, ha, he, hla⟩
  · have hh' : h ∈ P.funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, _, hf⟩
      · exact (site g hg info h hs).1
      · exact (Clif.Program.func?_some hf).1
    exact ⟨(facts hh').slots, (facts hh').size⟩
  · obtain ⟨n, -, hd, -⟩ := siteOk_sound (site_sound (facts hg).sites hs)
    exact ⟨n, hd⟩
  · obtain ⟨h', hf', hs⟩ := (facts hg).externs e he
    simp only [L] at hf
    rw [hf] at hf'; cases hf'; exact hs
  · obtain ⟨hh, hne, -⟩ := site g hg info h hs
    exact raCallB_sound (facts hg).ra hpc h hh hne
  · simp only [raStarB, List.all_eq_true, List.mem_range, bne_iff_ne] at hstar
    exact hstar h hh k hk
  · obtain ⟨n, h', hd, hf, -⟩ := siteOk_sound (site_sound (facts hg).sites hs)
    simp only [destOf, hd, LinkSys.BaseDest] at hb
    rcases hb with hb | ⟨n', hn, hb⟩
    · cases hb
    · cases hn; simp only [L] at hb; rw [hf] at hb; cases hb
  · intro ext hext
    simp only [L, List.mem_filter, Option.isNone_iff_eq_none] at hext
    obtain ⟨hm, hnone⟩ := hext
    obtain ⟨h', hf', -⟩ := (facts hg).externs ext hm
    rw [hf'] at hnone; cases hnone

end E2E.LinkWitness
