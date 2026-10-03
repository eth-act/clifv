import FV.E2E.LinkArm

/-! # Non-vacuity of `backend_correct_program` (docs/contracts/e2e.md, "Non-vacuity")

A concrete linked program for which every premise of `E2E.backend_correct_program` holds:
`P = {f, g, h, s, k}`, parsed from the embedded source `src`, compiled by the backend's pipeline
(`lowerFunction`, `prepare`, regalloc2's allocation `raOut` — the output of `lean-regalloc` on the
pipeline's input for this file, rebuilt by `buildRFunc` and accepted by `checkAlloc` —,
`lowerRFunc`, `emitFunc`, `layout`), loaded at `0x50000`, `0x20000`, `0x10000`, `0x30000`,
`0x40000`. The entry `f` has a stack slot and an outgoing-argument area; it calls

* `s` with an `sret` pointer to its slot (`s` stores through it, returns the pointer in x0),
* `k` with 9 arguments (the 9th on the stack, in `f`'s outgoing area),
* `g` by a `try_call` with a result (`g` calls `h`: a non-leaf program callee).

* The per-function premises of `LinkSys.Ok` are executable checks (`chks`, `okB`, each with a
  soundness lemma: `siteOk_sound`, `tryB_sound`, `retsB_sound`, `outFitsB_sound`,
  `entryB_sound`, `raCallB_sound`, `linkFreeB_sound`, `imgCode_of`, …), decided by
  `native_decide` (`okB_true`; the project's axiom policy allows `_native.native_decide` axioms).
* The base environment is closed: no extern outside `P` (`Xb.call` undefined), calls outside
  `P` continue at the next instruction (`Hb`), no TLS.
* **`L_ok`**: `(L F).Ok` for every `F` containing the code.
* **`backend_correct_program_witness`**: with the entry premises of `f` on the argument `41`
  (ABI entry state `s0`, body-entry world `w0`, CLIF entry state `cs0` with `f`'s slot at its
  frame address), the theorem applies: the linked machine refines `f`'s CLIF run, which returns
  `179`.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

def src : String := "function %h(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 1
    v2 = iadd v0, v1
    return v2
}

function %g(i64) -> i64 system_v {
    fn0 = colocated %h(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    v2 = iadd v1, v0
    return v2
}

function %s(i64 sret, i64) system_v {
block0(v0: i64, v1: i64):
    v2 = iconst.i64 7
    v3 = iadd v1, v2
    store.i64 notrap aligned v3, v0
    return
}

function %k(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64):
    v9 = iadd v0, v8
    return v9
}

function %f(i64) -> i64 system_v {
    ss0 = explicit_slot 8
    sig0 = (i64) -> i64 system_v
    fn0 = colocated %g(i64) -> i64 system_v
    fn1 = colocated %s(i64 sret, i64) system_v
    fn2 = colocated %k(i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 system_v
block0(v0: i64):
    v1 = stack_addr.i64 ss0
    call fn1(v1, v0)
    v2 = load.i64 notrap aligned v1
    v3 = iconst.i64 0
    v4 = call fn2(v2, v3, v3, v3, v3, v3, v3, v3, v0)
    try_call fn0(v4), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v5: i64):
    return v5
block2(v6: i64):
    return v6
}
"

def raOut : String := "{\"functions\":[{\"allocs\":[[\"x0\"],[\"x2\"],[\"x0\",\"x0\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"h\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x0\",\"x0\"],[\"x0\",\"x0\",\"x19\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":1,\"pos\":\"before\",\"to\":\"x19\"}],\"name\":\"g\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x8\",\"x0\"],[\"x3\"],[\"x5\",\"x0\"],[\"x5\",\"x8\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x8\",\"inst\":4,\"pos\":\"before\",\"to\":\"x0\"}],\"name\":\"s\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\",\"x1\",\"x2\",\"x3\",\"x4\",\"x5\",\"x6\",\"x7\"],[\"x9\"],[\"x0\",\"x0\",\"x9\"],[\"x0\"]],\"checker\":\"ok\",\"edits\":[],\"name\":\"k\",\"num_spillslots\":0,\"ok\":true},{\"allocs\":[[\"x0\"],[\"x8\"],[\"x8\",\"x0\",\"x0\"],[\"x0\"],[\"x7\"],[\"x19\"],[\"x0\",\"x1\",\"x2\",\"x3\",\"x4\",\"x5\",\"x6\",\"x7\",\"x0\"],[\"x0\",\"x0\",\"x1\"],[],[\"x0\"],[],[\"x0\"]],\"checker\":\"ok\",\"edits\":[{\"from\":\"x0\",\"inst\":2,\"pos\":\"before\",\"to\":\"x19\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x1\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x2\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x3\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x4\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x5\"},{\"from\":\"x7\",\"inst\":6,\"pos\":\"before\",\"to\":\"x6\"}],\"name\":\"f\",\"num_spillslots\":0,\"ok\":true}]}"

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
def fS : Clif.Function := fn 2
def fK : Clif.Function := fn 3
def fF : Clif.Function := fn 4

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

/-- The program `{f, g, h, s, k}`. -/
def P : Clif.Program := { funcs := [fF, fG, fH, fS, fK] }

/-- The file index of a function of `P` (the regalloc2 output and the local labels). -/
def idx (g : Clif.Function) : Nat :=
  if g = fF then 4 else if g = fG then 1 else if g = fS then 2 else if g = fK then 3 else 0

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

/-- A call site: a `bl` of a function `h` of `P` that `g` declares, arguments in `h`'s parameter
registers, results from x0.. (then, at a `try_call`, the exception payload registers). -/
def siteOk (P : Clif.Program) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => decide (h ≠ g) && g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (sigRets h.sig).length).map Reg.x)
    | none => false
  | .reg _ => false

theorem siteOk_sound {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOk P g info = true) :
    ∃ n h', info.dest = .sym n ∧ P.func? n = some h' ∧ h' ≠ g ∧
      (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      (Ld.map (·.1)).take (sigRets h'.sig).length =
        (List.range (sigRets h'.sig).length).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => simp at h
  | sym n =>
    cases hf : P.func? n with
    | none => simp [hf] at h
    | some h' =>
      simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨hne, hd⟩, hu⟩, hdd⟩, h1⟩, h2⟩ := h
      exact ⟨n, h', rfl, hf, hne, hd, _, _, by rw [← hu, ← hdd], h1, h2⟩

/-- A `try_call` of a function `h` of `P` takes at most `h`'s results. -/
def tryB (P : Clif.Program) : MInst → Bool
  | .tryCall info ti => match info.dest with
    | .sym n => match P.func? n with
      | some h => decide (ti.rets ≤ (sigRets h.sig).length)
      | none => true
    | .reg _ => true
  | _ => true

theorem tryB_sound {P : Clif.Program} {vc : VCode} (h : allInsts vc (tryB P) = true)
    {info : CallInfo} {ti : TryInfo} (hs : vc.TrySite info ti) {n : String} {h' : Clif.Function}
    (hd : info.dest = .sym n) (hf : P.func? n = some h') : ti.rets ≤ (sigRets h'.sig).length := by
  obtain ⟨b, vb, k, hb, hk⟩ := hs
  have := allInsts_sound h hb hk
  simpa [tryB, hd, hf] using this

/-- The returns of an `sret` function carry its ABI results. -/
def retsB (g : Clif.Function) : MInst → Bool
  | .rets us => !(g.sig.params.any (·.purpose == .sret)) || decide ((sigRets g.sig).length ≤ us.length)
  | _ => true

theorem retsB_sound {g : Clif.Function} {vc : VCode} (h : allInsts vc (retsB g) = true)
    (hs : g.sig.params.any (·.purpose == .sret) = true) {us : List (Reg × Reg)}
    (hr : vc.RetsSite us) : (sigRets g.sig).length ≤ us.length := by
  obtain ⟨b, vb, k, hb, hk⟩ := hr
  have := allInsts_sound h hb hk
  simpa [retsB, hs] using this

/-- The stack-passed parameters of `sig` fit an outgoing area of `ib` bytes. -/
def outFitsB (sig : Clif.Signature) (ib : Nat) : Bool :=
  (List.range (locsOf sig).length).all fun i => match (locsOf sig)[i]?, sig.params[i]? with
    | some (.stack off), some p => decide (off + p.ty.bytes ≤ ib)
    | _, _ => true

theorem outFitsB_sound {sig : Clif.Signature} {ib : Nat} (h : outFitsB sig ib = true) {i off : Nat}
    {p : Clif.AbiParam} (hl : (locsOf sig)[i]? = some (.stack off)) (hp : sig.params[i]? = some p) :
    off + p.ty.bytes ≤ ib := by
  have hi : i < (locsOf sig).length := (List.getElem?_eq_some_iff.mp hl).1
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa [hl, hp] using this

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

/-- `g` is called in `P`: a function of `P` declares it. -/
def calleeB (g : Clif.Function) : Bool :=
  P.funcs.any fun g' => g'.externs.any fun e => e.2.name == g.name

/-- The per-function checks. -/
def chks (g : Clif.Function) : List Bool :=
  let a := A g
  let fr := RAFrame.compute a.vcp a.rf
  [(pipe g (idx g) (baseOf g)).toBool, lowerCheck g a.vc, prepCheck a.vc a.vcp,
    (checkAlloc a.vcp a.rf).toBool, formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp,
    allInsts a.vcp (tryB P), allInsts a.vc (retsB g),
    g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase),
    decide (regLocs g.sig).Nodup, (regLocs g.sig).all (·.isArgReg),
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)),
    !calleeB g || (decide (g.slots = []) && (fr.size == a.af.frameSize && fr.intBase == 0)),
    allInsts a.vcp (siteB (siteOk P g)),
    g.externs.all (fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => false),
    entryB g a.vcp, decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64), raCallB P A g a,
    decide (frameDrop a.af ≤ 64), !hasTls g, linkFreeB g, Compile.functionE g,
    g.externs.all (fun e => e.2.name != g.name), sigAbiOk g.sig,
    g.externs.all (fun e => sigAbiOk e.2.sig), (indSigs g).isEmpty]

def chk (g : Clif.Function) : Bool := (chks g).all id

/-- All the executable checks. -/
def okB : Bool :=
  decide (P.funcs.map (·.name)).Nodup && (P.funcs.all chk && (imgB P A && raStarB P A 8))

theorem okB_true : okB = true := by native_decide

theorem okB_imgB : imgB P A = true := by
  have := okB_true
  simp only [okB, Bool.and_eq_true] at this
  exact this.2.2.1

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
  tries : allInsts (A g).vcp (tryB P) = true
  rets : allInsts (A g).vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, (P.func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute (A g).vcp (A g).rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB g = true → g.slots = [] ∧
    (RAFrame.compute (A g).vcp (A g).rf).size = (A g).af.frameSize ∧
    (RAFrame.compute (A g).vcp (A g).rf).intBase = 0
  sites : allInsts (A g).vcp (siteB (siteOk P g)) = true
  externs : ∀ e ∈ g.externs.map (·.2), ∃ h, P.func? e.name = some h ∧ e.sig = h.sig
  entry : entryB g (A g).vcp = true
  fits : (A g).base.toNat + 4 * (A g).fb.words.size ≤ 2 ^ 64
  ra : raCallB P A g (A g) = true
  depth : frameDrop (A g).af ≤ 64
  tls : hasTls g = false
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  extName : ∀ e ∈ g.externs.map (·.2), e.name ≠ g.name
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  ind : indSigs g = []

theorem toBool_unit {ε : Type} {x : Except ε Unit} (h : x.toBool = true) : x = .ok () := by
  cases x <;> simp_all [Except.toBool]

theorem chk_sound {g : Clif.Function} (h : chk g = true) : Facts g := by
  have hall : ∀ b ∈ chks g, b = true := by
    simpa [chk, List.all_eq_true] using h
  simp only [chks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h19 h22 h24
  refine ⟨getOk_eq h1, h2, h3, toBool_unit h4, (formsCoveredB_iff _ _).1 h5, h6, h7,
    fun e he hs => ?_, h9, h10, h11, fun hc => ?_, h13, fun e he => ?_, h15, h16, h17, h18, ?_,
    linkFreeB_sound h20, h21, fun e he => ?_, ⟨h23, h24⟩, List.isEmpty_iff.1 h25⟩
  · rcases h8 e he with h | h
    · simp [hs] at h
    · exact h
  · rcases h12 with h | h
    · simp [hc] at h
    · exact ⟨h.1, h.2.1, h.2.2⟩
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    have := h14 _ hm
    revert this
    cases hf : P.func? e'.name with
    | none => simp
    | some h => simp only [decide_eq_true_eq]; exact fun hs => ⟨h, rfl, hs⟩
  · simpa using h19
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    simpa using h22 _ hm

theorem facts {g : Clif.Function} (hg : g ∈ P.funcs) : Facts g := by
  have := okB_true
  simp only [okB, Bool.and_eq_true, List.all_eq_true] at this
  exact chk_sound (this.2.1 g hg)

/-! ## The linked program -/

/-- The link-time symbol addresses: every function at its base. -/
def symOf (n : String) : BitVec 64 :=
  if n = "f" then 0x50000 else if n = "g" then 0x20000 else if n = "h" then 0x10000
  else if n = "s" then 0x30000 else if n = "k" then 0x40000 else 0

/-- The base environment's machine semantics: no extern outside `P` (`call` undefined), the
symbols at the functions' bases. -/
def Xb : ExtSem where
  call _ _ _ := none
  sym n _ := symOf n
  tp := 0
  tlsFlags _ s := Arm.read_pstate s

/-- The base hooks: a call outside `P` continues at the next instruction; TLS keeps the state. -/
def Hb : ArmHooks := ⟨fun _ s => Arm.w .PC (Arm.r .PC s + 4) s, fun _ _ s => s⟩

/-- **The linked program** `{f, g, h, s, k}` with the addresses `F` outside the world. -/
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
  D := 64

theorem names : fF.name = "f" ∧ fG.name = "g" ∧ fH.name = "h" ∧ fS.name = "s" ∧ fK.name = "k" := by
  native_decide

theorem mem_P {g : Clif.Function} : g ∈ P.funcs ↔ g = fF ∨ g = fG ∨ g = fH ∨ g = fS ∨ g = fK := by
  simp [P]

theorem symOf_cases (n : String) : (n = "f" ∧ symOf n = 0x50000) ∨ (n = "g" ∧ symOf n = 0x20000) ∨
    (n = "h" ∧ symOf n = 0x10000) ∨ (n = "s" ∧ symOf n = 0x30000) ∨
    (n = "k" ∧ symOf n = 0x40000) ∨ symOf n = 0 := by
  unfold symOf
  by_cases h1 : n = "f"
  · simp [h1]
  by_cases h2 : n = "g"
  · simp [h2]
  by_cases h3 : n = "h"
  · simp [h3]
  by_cases h4 : n = "s"
  · simp [h4]
  by_cases h5 : n = "k"
  · simp [h5]
  simp [h1, h2, h3, h4, h5]

theorem symOf_eq {n m : String} (hm : m = "f" ∨ m = "g" ∨ m = "h" ∨ m = "s" ∨ m = "k")
    (h : symOf m = symOf n) : n = m := by
  rcases symOf_cases n with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | hn <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rw [hn] at h <;>
    first | rfl | (exfalso; revert h; simp (config := { decide := true }) [symOf])

theorem symInj {h : Clif.Function} (hh : h ∈ P.funcs) (n : String)
    (hn : Xb.sym h.name 0 = Xb.sym n 0) : n = h.name := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := names
  refine symOf_eq ?_ hn
  rcases mem_P.1 hh with rfl | rfl | rfl | rfl | rfl <;> simp [n1, n2, n3, n4, n5]

/-- **`L.Ok`**: every premise of the linked program, for every `F` containing the code. -/
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) : (L F).Ok := by
  have hok := okB_true
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnames, -, himg, hstar⟩ := hok
  have site : ∀ g ∈ P.funcs, ∀ info h, (L F).ProgSite g info h →
      h ∈ P.funcs ∧ h ≠ g ∧ calleeB h = true ∧ ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length = (List.range (sigRets h.sig).length).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    obtain ⟨n', h', hd', hf', hne, ⟨e, he, hen⟩, Lu, Ld, heq, h1, h2⟩ :=
      siteOk_sound (site_sound (facts hg).sites hs)
    rw [hd] at hd'; cases hd'
    have : h' = h := by simp only [L] at hf; rw [hf] at hf'; cases hf'; rfl
    subst this
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, hne, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, List.any_eq_true, beq_iff_eq]
    exact ⟨g, hg, e, he, by rw [hen, hname]⟩
  have noBase : ∀ g ∈ P.funcs, ∀ info, (A g).vcp.CallSite info → ¬ (L F).BaseDest (destOf info) := by
    intro g hg info hs hb
    obtain ⟨n, h', hd, hf, -⟩ := siteOk_sound (site_sound (facts hg).sites hs)
    simp only [destOf, hd, LinkSys.BaseDest] at hb
    rcases hb with hb | ⟨n', hn, hb⟩
    · cases hb
    · cases hn; simp only [L] at hb; rw [hf] at hb; cases hb
  refine
    { linkable := ⟨hnames, fun g hg => (facts hg).free⟩
      subset := fun g hg => ⟨?_, (facts hg).subsetE, ?_, ?_, (facts hg).abi, ?_⟩
      compiled := fun g hg => ?_
      covered := fun g hg => (facts hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := fun _ n gsem hn => by simp [L, Clif.Env.empty] at hn
      tryRets := fun g hg info ti h hs ⟨_, n, hd, hf⟩ => tryB_sound (facts hg).tries hs hd hf
      argRegs := fun g hg => ⟨(facts hg).nodup, (facts hg).argReg, (facts hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (facts hg).rets hs hr
      calleeSlots := fun g hg h hh => ?_
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2.2
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
      baseOs := fun g hg info hs hb => absurd hb (noBase g hg info hs)
      basePc := fun d s _ _ _ => by simp [L, Hb, Arm.r_of_w_same]
      baseExt := fun d uses w outs w' _ hx => by simp [L, Xb] at hx
      baseX := fun g hg F' slotOff out c => ?_
      baseTls := fun g hg ht => absurd ht (by simp [L, (facts hg).tls])
      baseTry := fun g hg F' _ info _ hs => absurd hs.2 (noBase g hg info hs.1.callSite) }
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
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    exact outFitsB_sound ((facts hg).outFits _ hm hs) hl hp
  · have hc : calleeB h = true ∧ h ∈ P.funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, he, hf⟩
      · obtain ⟨hh', -, hc, -⟩ := site g hg info h hs
        exact ⟨hc, hh'⟩
      · obtain ⟨hh', hname⟩ := Clif.Program.func?_some hf
        refine ⟨?_, hh'⟩
        obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
        simp only [calleeB, List.any_eq_true, beq_iff_eq]
        exact ⟨g, hg, (fn, e'), hm, hname.symm⟩
    exact (facts hc.2).callee hc.1
  · obtain ⟨n, -, hd, -⟩ := siteOk_sound (site_sound (facts hg).sites hs)
    exact ⟨n, hd⟩
  · obtain ⟨h', hf', hs⟩ := (facts hg).externs e he
    simp only [L] at hf
    rw [hf] at hf'; cases hf'; exact hs
  · obtain ⟨hh, hne, -⟩ := site g hg info h hs
    exact raCallB_sound (facts hg).ra hpc h hh hne
  · simp only [raStarB, List.all_eq_true, List.mem_range, bne_iff_ne] at hstar
    exact hstar h hh k hk
  · intro ext hext
    simp only [L, List.mem_filter, Option.isNone_iff_eq_none] at hext
    obtain ⟨hm, hnone⟩ := hext
    obtain ⟨h', hf', -⟩ := (facts hg).externs ext hm
    rw [hf'] at hnone; cases hnone

/-! ## A concrete entry of `f` -/

/-- The call depth of the witness run. -/
def M0 : Nat := 20

def sp0 : BitVec 64 := 0x100000

/-- The argument `41 : i64`. -/
def arg : Clif.Val := ⟨.i64, 41#64⟩

/-- The entry block of `f`. -/
def bF : Clif.Block := fF.entry?.getD default

/-- The address of `f`'s stack slot `ss0` in its frame: the body's `sp` (`sp0 - 64`) plus the
slot base `32`. -/
def slotAddr : Nat := 0x100000 - 32

/-- The CLIF entry state of `f` on `41`: its slot at its frame address, the memory holding that
(uninitialised) allocation only. -/
def cs0 : Clif.State where
  frame := { func := fF, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).getD default,
             slots := [(0, slotAddr)], body := bF.body, term := bF.term }
  callers := []
  mem := { allocs := [{ base := slotAddr, size := 8 }] }

/-- The CLIF run of the program from `cs0`. -/
def run0 : Clif.Outcome := Clif.runLoop Clif.Env.empty P (M0 + 1) cs0

def retVals : Clif.Outcome → List Clif.Val
  | .returned v _ => v
  | _ => []

def retMem : Clif.Outcome → Clif.Mem
  | .returned _ m => m
  | _ => Clif.Mem.empty

def isRet : Clif.Outcome → Bool
  | .returned _ _ => true
  | _ => false

theorem eq_returned {o : Clif.Outcome} (h : isRet o = true) : o = .returned (retVals o) (retMem o) := by
  cases o <;> simp_all [isRet, retVals, retMem]

/-- Every code address of `P` is in `[0x10000, 0x60000)`. -/
def boundB : Bool :=
  P.funcs.all fun g => let a := A g
    decide (a.base.toNat + 4 * a.fb.words.size + 4 ≤ 0x60000)

def locB : Bool :=
  match locsOf fF.sig with
  | [.reg (.x 0)] => true
  | _ => false

/-- The frame of `f`: 64 bytes below the entry `sp` (fp/lr, a 48-byte frame: the 16-byte
outgoing area, 16 bytes of saves, the 8-byte slot at `32`). -/
def frameB : Bool :=
  (A fF).af.frame && decide (frameDrop (A fF).af = 64) && decide ((A fF).af.frameSize = 48) &&
  decide ((A fF).af.slotBase = 32) && decide ((RAFrame.compute (A fF).vcp (A fF).rf).intBase = 16) &&
  decide ((RAFrame.compute (A fF).vcp (A fF).rf).size = 32) &&
  decide ((slotLayout fF.slots).1 = [(0, 0)]) && decide (fF.slots.map (·.1) = [0])

/-- The entry facts of `f` and its run: `f 41 = h (k (s 41, 0, …, 41)) + …` returns `179`. -/
def entryFactsB : Bool :=
  boundB && locB && frameB &&
  decide (P.func? fF.name = some fF) && decide (fF.entry? = some bF) &&
  decide ([arg].map (·.ty) = fF.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = [arg].map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).isSome &&
  isRet run0 && decide (retVals run0 = [⟨.i64, 179#64⟩])

theorem entryFactsB_true : entryFactsB = true := by native_decide

theorem entryFacts :
    boundB = true ∧ locB = true ∧ frameB = true ∧ P.func? fF.name = some fF ∧
    fF.entry? = some bF ∧ [arg].map (·.ty) = fF.sig.params.map (·.ty) ∧
    bF.params.map (·.2) = [arg].map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) [arg]).isSome = true ∧ isRet run0 = true ∧
    retVals run0 = [⟨.i64, 179#64⟩] := by
  have he := entryFactsB_true
  simp only [entryFactsB, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := he
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem frameFacts :
    (A fF).af.frame = true ∧ frameDrop (A fF).af = 64 ∧ (A fF).af.frameSize = 48 ∧
    (A fF).af.slotBase = 32 ∧ (RAFrame.compute (A fF).vcp (A fF).rf).intBase = 16 ∧
    (RAFrame.compute (A fF).vcp (A fF).rf).size = 32 ∧ (slotLayout fF.slots).1 = [(0, 0)] ∧
    fF.slots.map (·.1) = [0] := by
  have h := entryFacts.2.2.1
  simp only [frameB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem wordsAt_mem_inv {base : BitVec 64} {p : BitVec 64 × BitVec 32} :
    ∀ {ws : List (BitVec 32)} {k : Nat}, List.Mem p (wordsAt base k ws) →
      ∃ j < ws.length, p.1 = base + BitVec.ofNat 64 (4 * (k + j))
  | [], _, h => nomatch h
  | x :: ws, k, h => by
    cases h with
    | head => exact ⟨0, by simp, by simp⟩
    | tail _ h =>
      obtain ⟨j, hj, e⟩ := wordsAt_mem_inv h
      exact ⟨j + 1, by simp; omega, by rw [e]; congr 2; omega⟩

theorem codeAddr_lt {a : Art} (hb : a.base.toNat + 4 * a.fb.words.size + 4 ≤ 0x60000) {x : BitVec 64}
    {t : Arm.ArmState} (ht : t.program = a.fb.program a.base) (h : CodeAddr t x) :
    x.toNat < 0x60000 := by
  obtain ⟨p, hp, hx⟩ := h
  rw [ht] at hp
  obtain ⟨j, hj, e⟩ := wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := a.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

theorem bound_of {g : Clif.Function} (hg : g ∈ P.funcs) :
    (A g).base.toNat + 4 * (A g).fb.words.size + 4 ≤ 0x60000 := by
  have h := entryFacts.1
  simp only [boundB, List.all_eq_true, decide_eq_true_eq] at h
  exact h g hg

theorem img_lt {x : BitVec 64} (h : Img P A x) : x.toNat < 0x60000 := by
  obtain ⟨g, hg, hc⟩ := h
  exact codeAddr_lt (bound_of hg) rfl hc

/-- The ABI entry state of `f`: its code loaded at its base (program and memory, the image of
the whole program in memory), the argument `41` in x0, `sp = 0x100000`, return address `8`. -/
def s0 : Arm.ArmState :=
  Arm.w .PC (A fF).base (Arm.w (.GPR 30#5) 8 (Arm.w (.GPR 31#5) sp0 (Arm.w (.GPR 0#5) 41#64
    (setMem (Arm.set_program Arm.ArmState.default ((A fF).fb.program (A fF).base))
      (memOf (progAll P A))))))

/-- The body-entry world: after the prologue (`stp x29, x30, [sp, #-16]!; mov x29, sp;
sub sp, sp, #48`). -/
def w0 : Arm.ArmState := Arm.w (.GPR 31#5) (sp0 - 64) (Arm.w (.GPR 29#5) (sp0 - 16) s0)

/-- The addresses outside the world of the entry activation: its frame, its callees' stack,
the code. -/
def F0 : BitVec 64 → Prop :=
  frameWG (64 * M0) (RAFrame.compute (A fF).vcp (A fF).rf).intBase
    (RAFrame.compute (A fF).vcp (A fF).rf).size (A fF).af (Img P A) s0

theorem mem_w (f : Arm.StateField) (v : Arm.state_value f) (s : Arm.ArmState) :
    (Arm.w f v s).mem = s.mem :=
  funext fun a => (Arm.read_mem_of_w (addr := a) (fld := f) (v := v) (s := s) :)

theorem s0_mem : s0.mem = memOf (progAll P A) := by simp [s0, mem_w]

theorem s0_program : s0.program = (A fF).fb.program (A fF).base := by
  simp [s0, Arm.w_program]

theorem spv_s0 : spv s0 = sp0 := by simp [s0, spv, Arm.r_of_w_different, Arm.r_of_w_same]

theorem spv_w0 : spv w0 = sp0 - 64 := by simp [w0, spv, Arm.r_of_w_same]

/-- The frame of `f` above its body `sp`, outside the spill/save area `[16, 32)` and fp/lr
`[48, 64)`, and the outgoing area `[0, 16)` belong to the world. -/
theorem not_F0 {x : BitVec 64} (h1 : 0xFFFC0 ≤ x.toNat) (h2 : x.toNat < 0x100000)
    (h3 : ¬ (0xFFFD0 ≤ x.toNat ∧ x.toNat < 0xFFFE0)) (h4 : x.toNat < 0xFFFF0) : ¬ F0 x := by
  obtain ⟨hfr, hd, hfs, -, hib, hsz, -⟩ := frameFacts
  have hbody : (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af)).toNat = 0xFFFC0 := by
    rw [spv_s0, hd]; decide
  have hsub : (x - (spv s0 - BitVec.ofNat 64 (frameDrop (A fF).af))).toNat = x.toNat - 0xFFFC0 := by
    rw [spv_s0, hd]
    simp only [sp0]
    bv_omega
  simp only [F0, frameWG, frameW, frameF, StackBelow, hib, hsz, hsub, hbody, hfs]
  rintro (((⟨ha, hb⟩ | ⟨ha, hb⟩ | hc) | ⟨hlt, -⟩) | hi)
  · omega
  · rw [hd] at hb; omega
  · have := codeAddr_lt (bound_of (g := fF) (by simp [P])) s0_program hc; omega
  · omega
  · have := img_lt hi; omega

theorem gpr_ne {i j : Nat} (hi : i < 32) (hj : j < 32) (h : i ≠ j) :
    Arm.StateField.GPR (BitVec.ofNat 5 i) ≠ .GPR (BitVec.ofNat 5 j) := by
  intro e
  injection e with e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- `vc` has a `call` of the symbol `n`. -/
def callsB (vc : VCode) (n : String) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .call info => decide (info.dest = .sym n)
    | _ => false

theorem callsB_sound {vc : VCode} {n : String} (h : callsB vc n = true) :
    ∃ info, vc.CallSite info ∧ info.dest = .sym n := by
  simp only [callsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i info e
    intro hd
    exact ⟨info, ⟨b, _, k, Array.getElem?_eq_getElem hb, .inl (by rw [Array.getElem?_eq_getElem hk, e])⟩,
      of_decide_eq_true hd⟩
  · simp

/-- `vc` has a `try_call` of the symbol `n`. -/
def tryCallsB (vc : VCode) (n : String) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun i => match i with
    | .tryCall info _ => decide (info.dest = .sym n)
    | _ => false

theorem tryCallsB_sound {vc : VCode} {n : String} (h : tryCallsB vc n = true) :
    ∃ info ti, vc.TrySite info ti ∧ info.dest = .sym n := by
  simp only [tryCallsB, Array.any_eq_true] at h
  obtain ⟨b, hb, k, hk, hi⟩ := h
  revert hi
  split
  · rename_i info ti e
    intro hd
    exact ⟨info, ti, ⟨b, _, k, Array.getElem?_eq_getElem hb, by rw [Array.getElem?_eq_getElem hk, e]⟩,
      of_decide_eq_true hd⟩
  · simp

/-- `f` calls `s` (an `sret` callee), `k` (a stack-passed argument) and `g` by a `try_call`;
`g` calls `h` (in their compiled code). -/
def callChainB : Bool :=
  tryCallsB (A fF).vcp "g" && callsB (A fG).vcp "h" && callsB (A fF).vcp "s" &&
  callsB (A fF).vcp "k" &&
  decide (P.func? "g" = some fG) && decide (P.func? "h" = some fH) &&
  decide (P.func? "s" = some fS) && decide (P.func? "k" = some fK) &&
  fS.sig.params.any (·.purpose == .sret) &&
  (locsOf fK.sig).any (fun l => match l with | .stack _ => true | .reg _ => false)

theorem callChainB_true : callChainB = true := by native_decide

/-- **Non-vacuity of `backend_correct_program`**: for the program `P = {f, g, h, s, k}` — `f`
passes an `sret` pointer to its stack slot to `s`, a stack-passed argument to `k` and calls `g`
by a `try_call` with a result; `g` calls `h` (a non-leaf callee) —, compiled by the backend's
pipeline (regalloc2's allocation, accepted by `checkAlloc`), linked at `0x50000`, `0x20000`,
`0x10000`, `0x30000`, `0x40000`, every premise of the theorem holds — `L.Ok` and the entry
premises of `f` on the argument `41` — and the theorem gives: the linked Arm machine refines
`f`'s CLIF run, which returns `179`. -/
theorem backend_correct_program_witness :
    (L F0).Ok ∧ fF ∈ (L F0).P.funcs ∧ fG ∈ (L F0).P.funcs ∧ fH ∈ (L F0).P.funcs ∧
    fS ∈ (L F0).P.funcs ∧ fK ∈ (L F0).P.funcs ∧
    (∃ info ti, (A fF).vcp.TrySite info ti ∧ (L F0).ProgSite fF info fG) ∧
    (∃ info, (L F0).ProgSite fG info fH) ∧
    (∃ info, (L F0).ProgSite fF info fS) ∧ fS.sig.params.any (·.purpose == .sret) = true ∧
    (∃ info, (L F0).ProgSite fF info fK) ∧ (∃ off, ArgLoc.stack off ∈ locsOf fK.sig) ∧
    (RAFrame.compute (A fF).vcp (A fF).rf).intBase ≠ 0 ∧ fF.slots ≠ [] ∧
    run0 = .returned [⟨.i64, 179#64⟩] (retMem run0) ∧
    ArmRefines (A fF).fb (A fF).base 8 ((L F0).mach M0 fF) s0 run0 := by
  have hF : ∀ a, Img P A a → F0 a := fun a ha => .inr ha
  have hL := L_ok F0 hF
  have hfF : fF ∈ (L F0).P.funcs := by simp [L, P]
  have hc := callChainB_true
  simp only [callChainB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcf, hcg⟩, hcs⟩, hck⟩, hpg⟩, hph⟩, hps⟩, hpk⟩, hsret⟩, hstk⟩ := hc
  obtain ⟨hbound, hloc, -, hfunc, hentry, hsig, hparams, hset, hret, hvals⟩ := entryFacts
  obtain ⟨hframe, hdrop, hfs, hsb, hib, hsz, hlay, hslots⟩ := frameFacts
  have hrun : run0 = .returned [⟨.i64, 179#64⟩] (retMem run0) := by
    rw [← hvals]; exact eq_returned hret
  have hfa := facts (g := fF) (by simp [P])
  have hlocs : locsOf fF.sig = [.reg (.x 0)] := by
    unfold locB at hloc
    split at hloc
    · assumption
    · cases hloc
  have hbF : (A fF).base.toNat + 4 * (A fF).fb.words.size + 4 ≤ 0x60000 := bound_of (by simp [P])
  refine ⟨hL, hfF, by simp [L, P], by simp [L, P], by simp [L, P], by simp [L, P], ?_, ?_, ?_,
    hsret, ?_, ?_, by rw [hib]; decide, fun h => by simp [h] at hslots, hrun, ?_⟩
  · obtain ⟨info, ti, hs, hd⟩ := tryCallsB_sound hcf
    exact ⟨info, ti, hs, hs.callSite, "g", hd, hpg⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcg
    exact ⟨info, hs, "h", hd, hph⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hcs
    exact ⟨info, hs, "s", hd, hps⟩
  · obtain ⟨info, hs, hd⟩ := callsB_sound hck
    exact ⟨info, hs, "k", hd, hpk⟩
  · obtain ⟨l, hl, hst⟩ := List.any_eq_true.mp hstk
    cases l with
    | stack off => exact ⟨off, hl⟩
    | reg _ => cases hst
  rw [hrun]
  refine backend_correct_program_returned (L F0) hL hfF M0 (w₀ := w0) (args := [arg]) (cs := cs0)
    ?hent ?hres rfl ?hgfree ?himg ?hbe ?hargs ?hcs ?hsav ?hrel (hrun ▸ rfl)
  case hent =>
    refine ⟨s0_program, imgCode_of (okB_imgB) (by simp [P]) s0 (fun a _ => by rw [s0_mem]),
      by simp [s0, L, Arm.r_of_w_same], ?_, ?_, hL.raStar fF hfF, ?_, hL.fits fF hfF⟩
    · simp [s0, Arm.r_of_w_different, r_setMem, r_set_program, Arm.r, Arm.read_base_error,
        Arm.ArmState.default]
    · simp [s0, xreg, Arm.r_of_w_different, Arm.r_of_w_same]
    · rw [spv_s0]; decide
  case hres =>
    refine ⟨by simp [L, LinkSys.K, hfs, spv_s0, sp0, M0], fun a ha => ?_⟩
    have hlt := codeAddr_lt hbF s0_program ha
    simp only [L, LinkSys.K, hfs, spv_s0, sp0, M0]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (1048576 : BitVec 64).toNat = 1048576 := rfl
    omega
  case hgfree =>
    intro a ha ⟨h1, h2⟩
    have hlt := img_lt ha
    simp only [L, LinkSys.K, hdrop, spv_s0, sp0, M0] at h1 h2
    simp at h2
    omega
  case himg => exact fun a _ => by rw [s0_mem]; rfl
  case hbe =>
    refine ⟨?_, ?_, fun i hi => ?_, fun i _ => ?_, fun f _ h29 h31 => ?_, ?_, ?_⟩
    · simp only [L, hdrop, spv_s0]; simp [w0, spv, Arm.r_of_w_same]
    · simp only [L, hframe, ite_true, spv_s0]; simp [w0, xreg, Arm.r_of_w_different, Arm.r_of_w_same]
    · simp only [xreg, w0]
      rw [Arm.r_of_w_different (gpr_ne (by omega) (by omega) (by omega : i ≠ 31)),
        Arm.r_of_w_different (gpr_ne (by omega) (by omega) (by omega : i ≠ 29))]
    · simp [w0, Arm.r_of_w_different]
    · simp only [w0]; rw [Arm.r_of_w_different h31, Arm.r_of_w_different h29]
    · simp [w0, mem_w]
    · simp [w0, Arm.w_program]
  case hargs =>
    intro loc v hm
    rw [hlocs] at hm
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [VHolds, regVal, rnum, s0, Arm.r_of_w_different, Arm.r_of_w_same, arg]
    rfl
  case hcs =>
    refine ⟨rfl, rfl, hsig, ⟨bF, hentry, rfl, rfl, hparams, ?_⟩, by simp [cs0, hslots]⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hset
    simp only [cs0, hr, Option.getD_some]
  case hsav =>
    intro off v hm
    rw [hlocs] at hm
    simp at hm
  case hrel =>
    have hvalid : ∀ a n, cs0.mem.valid a n = true → slotAddr ≤ a ∧ a + n ≤ slotAddr + 8 := by
      intro a n h
      simp [cs0, Clif.Mem.valid, Clif.Alloc.contains] at h
      omega
    refine ⟨⟨fun a b ha hb => by simp [cs0] at hb, fun a n ha => ?_, rfl⟩,
      fun id b h => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hvalid a n ha
      refine ⟨by simp [slotAddr] at h2 ⊢; omega, fun k hk => not_F0 ?_ ?_ ?_ ?_⟩ <;>
        simp only [BitVec.toNat_ofNat, slotAddr] at h1 h2 ⊢ <;>
        rw [Nat.mod_eq_of_lt (by omega)] <;> omega
    · simp only [cs0, List.lookup] at h
      split at h
      · rename_i e
        cases h
        have hid : id = 0 := by simpa using e
        subst hid
        refine ⟨0, by rw [hlay]; rfl, ?_⟩
        simp only [Rel.slotReg, spv_w0, sp0, slotAddr]
        rw [show ((L F0).A fF) = A fF from rfl, hsb]
        decide
      · cases h
    · show OutRel _ (RAFrame.compute (A fF).vcp (A fF).rf).intBase _ _
      rw [hib]
      refine ⟨by decide, fun j hj => not_F0 ?_ ?_ ?_ ?_, fun a n ha k hk j hj e => ?_⟩
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · rw [spv_w0]; simp only [sp0]; bv_omega
      · obtain ⟨h1, h2⟩ := hvalid a n ha
        rw [spv_w0] at e
        have := congrArg BitVec.toNat e
        simp only [sp0, slotAddr] at this h1 h2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        bv_omega

end E2E.LinkWitness
