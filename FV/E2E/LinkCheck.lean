import FV.E2E.LinkArm
import FV.Opt.Legalize128Pass

/-! # A decidable checker for `LinkSys.Ok` (docs/contracts/e2e.md, "Crate-level instance")

`backend_correct_program` (`FV/E2E/LinkArm.lean`) needs `L.Ok` for a linked system `L`. Here
`L` is rebuilt from the data a build of a crate leaves behind (`cargo fv --keep-temps`, then
`cargo fv link-proof`):

* `LinkInput`: per function the CLIF file `lean-backend` compiled and `lean-regalloc`'s output
  for it; the link map's symbol addresses (`addrs`); the CLIF image's symbols (`syms`: the names
  the program's CLIF takes the address of); a return address outside all code (`raStar`); the
  stack of one call level (`D`).
* `LinkSys.ofInput I B F`: the program is the parsed (and `i128`-legalised, as `lean-backend`
  does) functions, each compiled by the pipeline in Lean (`lowerFunction`, `prepare`,
  `parseRAOut`/`buildRFunc`, `lowerRFunc`, `emitFunc`, `layout`) and loaded at its link-map
  address; `Xb.sym` is the link map; the code image is the compiled words. The base environment
  `B` (the CLIF semantics and machine hooks of everything outside the program: std, other
  crates' cg_clif code, the runtime) is a parameter.
* `okB I : Bool` evaluates every per-function and layout premise of `LinkSys.Ok`; `okB_sound`:
  `okB I = true → BaseOk (ofInput I B F) → (∀ a, Img a → F a) → (ofInput I B F).Ok`. `BaseOk`
  collects exactly the premises of `LinkSys.Ok` about the base environment (its contracts),
  which no check on the program can discharge: they stay premises of the crate's theorem
  (`CrateStmt`, `crate_correct`).
* `diag I`: the failing checks by function and premise (`lake exe link-check`).

The executable checks repeat `FV/E2E/NonVacuityLink.lean`'s (whose closed program has no base
externs), generalised: calls of externs outside the program are allowed (the base contracts),
`tls_value` is allowed (`baseTls`), the symbol tables are data.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Inputs -/

/-- One function: the CLIF file `lean-backend` compiled, its index `k` there, and the output of
`lean-regalloc` on that file with the function's index `j` in it. -/
structure FnInput where
  clif : String
  ra : String
  k : Nat := 0
  j : Nat := 0
  deriving Inhabited

/-- **The input of a crate-level instance**: the program's functions; the link map (`addrs`:
every symbol's address, `Xb.sym`); the CLIF image's symbol table (`syms`: `L.syms`, the
`symbol_value`/`func_addr` names of the program's CLIF with their addresses); a return address
outside all code (`raStar`); the stack of one call level (`D`). -/
structure LinkInput where
  funcs : List FnInput
  addrs : List (String × Nat)
  syms : List (String × Nat)
  raStar : Nat
  D : Nat
  deriving Inhabited

deriving instance Inhabited for Art

def getOk {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok a => a
  | .error _ => default

theorem getOk_eq {ε α : Type} [Inhabited α] {x : Except ε α} (h : x.toBool = true) :
    x = .ok (getOk x) := by
  cases x <;> simp_all [getOk, Except.toBool]

theorem toBool_unit {ε : Type} {x : Except ε Unit} (h : x.toBool = true) : x = .ok () := by
  cases x <;> simp_all [Except.toBool]

/-- The function the file holds at index `k`, after the `i128` legalisation `lean-backend`
applies (the identity on functions without `i128`). -/
def FnInput.func (fi : FnInput) : Clif.Function :=
  match (Opt.Legalize128.parsedFile128 (Clif.parseFile fi.clif)).file.funcs[fi.k]? with
  | some p => getOk p.func
  | none => default

/-- Function `j` of a `lean-regalloc` output. -/
def raJ (ra : String) (j : Nat) : Lean.Json :=
  (((getOk (Lean.Json.parse ra)).getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
    |>.getD j default

/-- The link-map address of `n` (`0` when it has none). -/
def LinkInput.addrOf (I : LinkInput) (n : String) : Nat := (I.addrs.lookup n).getD 0

/-- The machine's link-time symbol addresses: the link map. -/
def LinkInput.symAddr (I : LinkInput) (n : String) (off : Int) : BitVec 64 :=
  BitVec.ofNat 64 (I.addrOf n) + BitVec.ofInt 64 off

/-- The pipeline on `f` (index `k` in its file, regalloc output `o`) loaded at `base`. -/
def pipe (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare vc
  let o ← parseRAOut o
  let rf ← buildRFunc vcp o
  let af ← lowerRFunc vcp rf
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, rf, af, fa, fb, base⟩

theorem pipe_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipe f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipe at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : parseRAOut o with _ | o' <;> simp only [h3] at h
  · cases h
  rcases h4 : buildRFunc vcp o' with _ | rf <;> simp only [h4] at h
  · cases h
  rcases h5 : lowerRFunc vcp rf with _ | af <;> simp only [h5] at h
  · cases h
  rcases h6 : emitFunc k af with _ | fa <;> simp only [h6] at h
  · cases h
  rcases h7 : fa.layout with _ | fb <;> simp only [h7] at h
  · cases h
  cases h
  exact ⟨rfl, h2, h5, h6, h7, rfl, rfl⟩

/-- The program's functions with their pipeline results (computed once by the checker). -/
abbrev Res := List (Clif.Function × Except String Art)

/-- Every function of the input, compiled and loaded at its link-map address. -/
def LinkInput.results (I : LinkInput) : Res :=
  I.funcs.map fun fi => let f := fi.func
    (f, pipe f fi.k (BitVec.ofNat 64 (I.addrOf f.name)) (raJ fi.ra fi.j))

def progOf (R : Res) : Clif.Program := { funcs := R.map (·.1) }

/-- The compiled images (an error is the default image; the checker rejects it). -/
def tabOf (R : Res) : List (Clif.Function × Art) := R.map fun e => (e.1, getOk e.2)

/-- The compiled image of `g` (looked up by name). -/
def artOf (R : Res) (g : Clif.Function) : Art :=
  match R.find? (fun e => e.1.name == g.name) with
  | some e => getOk e.2
  | none => default

/-! ## The linked system -/

/-- **The base environment**: everything outside the program — the CLIF semantics of the
externs outside `P` (`env`), their machine semantics (`call`), the thread pointer and the
TLSDESC flags, and the machine's hooks for calls outside `P` and TLS. -/
structure BaseEnv where
  env : Clif.Env
  call : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)
  tp : BitVec 64
  tlsFlags : String → Arm.ArmState → Arm.PState
  hooks : ArmHooks

/-- The code words of the compiled functions by address. -/
def wordMap (T : List (Clif.Function × Art)) : Std.HashMap (BitVec 64) (BitVec 32) :=
  T.foldl (fun m e => (List.range e.2.fb.words.size).foldl
    (fun m k => m.insert (e.2.base + BitVec.ofNat 64 (4 * k)) e.2.fb.words[k]!) m) {}

/-- **The code image**: the byte at `a` of the word at `a` rounded down to 4 bytes (the
checker's `imgB` reads every word back from it, so overlapping or misaligned code is rejected). -/
def memT (T : List (Clif.Function × Art)) : Arm.Memory :=
  let m := wordMap T
  fun a => match m[a &&& ~~~3#64]? with
    | some w => w.extractLsb' (8 * (a &&& 3#64).toNat) 8
    | none => 0

/-- The code addresses of the compiled functions. -/
def ImgT (T : List (Clif.Function × Art)) (a : BitVec 64) : Prop :=
  ∃ e ∈ T, CodeAddr (Arm.set_program Arm.ArmState.default (e.2.fb.program e.2.base)) a

/-- **The linked system of an input** with the program's results `R`, base environment `B` and
the addresses `F` outside the entry activation's world. -/
def ofRes (I : LinkInput) (R : Res) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys where
  P := progOf R
  A := artOf R
  base := B.env
  Xb := { call := B.call, sym := I.symAddr, tp := B.tp, tlsFlags := B.tlsFlags }
  Hb := B.hooks
  syms := fun n => I.syms.lookup n
  F := F
  Img := ImgT (tabOf R)
  imgMem := memT (tabOf R)
  raStar := BitVec.ofNat 64 I.raStar
  D := I.D

/-- **`LinkSys.ofInput`**: the linked system of a crate's input. -/
def _root_.E2E.LinkSys.ofInput (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes I I.results B F

/-- **The base environment's premises** of `LinkSys.Ok`: the contracts of the calls outside
the program and of TLS, as `LinkSys.Ok` states them (each gated as there), plus the symbol
keeping of `Clif.IndScope` (needed only with indirect calls). They are not about the compiled
program, so no check decides them: they stay premises of the crate's theorem. -/
structure BaseOk (L : LinkSys) : Prop where
  baseNoAlloc : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    NoAllocEnv L.base
  keepSyms : (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → Opt.EnvKeepsSymbols L.base
  baseOs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ F K G s0 Pc ctx, CallSoundCtlG F K G s0 Pc (callExec L.Hb) (csem F ctx L.Xb) (.call info) .next
  basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (L.Hb.call d s) = Arm.r .PC s + 4
  baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseX : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsOk L.base
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseXI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsIndOk L.base (indSigs g)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseTls : ∀ g ∈ L.P.funcs, hasTls g = true → ∀ F K, TlsOk F K L.Xb L.Hb
  baseTry : ∀ g ∈ L.P.funcs, ∀ F, CalleeTryOk F L.Xb L.Hb
    fun info ti => (L.A g).vcp.TrySite info ti ∧ L.BaseDest (destOf info)
  baseNI : L.NeedNI → ∀ g ∈ L.P.funcs, ∀ F c, XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
    (fun n sig vals cm => L.P.func? n = none ∧
      CallLg L.base (g.externs.map (·.2)) (indSigs g) n sig vals cm) L.Xb
  baseTlsNI : L.NeedNI → ∀ F, XTls F L.Xb
  baseKeepsPlace : L.NeedSlots → Clif.EnvKeepsPlace L.base
  baseKeepsAllocs : L.NeedSlots → Clif.EnvKeepsAllocs L.base

/-! ## Executable checks -/

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

/-- `g` declares `n`, other than itself (`DeclN`). -/
def declB (g : Clif.Function) (n : String) : Bool :=
  g.externs.any (fun e => e.2.name == n) && n != g.name

theorem declB_of {g : Clif.Function} {n : String} (h : DeclN g n) : declB g n = true := by
  obtain ⟨hm, hne⟩ := h
  obtain ⟨e, he, hen⟩ := List.mem_map.mp hm
  simp only [declB, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨e, he, hen⟩, hne⟩

/-- A `blr` site: arguments in the parameter registers, results from x0.., of every function of
`P` that `g` declares with as many register parameters. -/
def blrOk (P : Clif.Program) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .reg (.vreg _ .int) =>
    decide (info.uses = retPairs (decU info.uses)) &&
    decide (info.defs = callDefs (decD info.defs)) &&
    P.funcs.all fun h => !declB g h.name ||
      decide ((regLocs h.sig).length ≠ (decU info.uses).length) ||
      (decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (sigRets h.sig).length).map Reg.x))
  | _ => false

theorem blrOk_sound {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : blrOk P g info = true) :
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ P.funcs, DeclN g h.name → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length = (List.range (sigRets h.sig).length).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold blrOk at h
  split at h
  · rename_i t hd
    simp only at hd
    subst hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨hu, hd⟩, hall⟩ := h
    refine ⟨t, decU us, decD ds, by rw [← hu, ← hd], fun h' hh hdecl hl => ?_⟩
    rcases hall h' hh with (h1 | h1) | h1
    · rw [declB_of hdecl] at h1; cases h1
    · exact absurd hl h1
    · exact h1
  · cases h

/-- A call site: a `bl` of a function `h` of `P` (other than `g`) that `g` declares, arguments in
`h`'s parameter registers, results from x0.. (then, at a `try_call`, the exception payload
registers); a `bl` of an extern outside `P` (the base's contract); or a `blr` site (`blrOk`). -/
def siteOk (P : Clif.Program) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => (h.name != g.name) && g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (sigRets h.sig).length).map Reg.x)
    | none => true
  | .reg _ => blrOk P g info

theorem siteOk_reg {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOk P g info = true) (hd : ∀ n, info.dest ≠ .sym n) : blrOk P g info = true := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => exact h
  | sym n => exact absurd rfl (hd n)

theorem siteOk_sound {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOk P g info = true) {n : String} {h' : Clif.Function} (hd : info.dest = .sym n)
    (hf : P.func? n = some h') :
    h'.name ≠ g.name ∧ (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      (Ld.map (·.1)).take (sigRets h'.sig).length =
        (List.range (sigRets h'.sig).length).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  unfold siteOk at h
  simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hne, hd⟩, hu⟩, hdd⟩, h1⟩, h2⟩ := h
  exact ⟨hne, hd, _, _, by rw [← hu, ← hdd], h1, h2⟩

/-- A `try_call` of a function `h` of `P` takes at most `h`'s results (at a `blr`: of every
declared function with as many register parameters). -/
def tryB (P : Clif.Program) (g : Clif.Function) : MInst → Bool
  | .tryCall info ti => match info.dest with
    | .sym n => match P.func? n with
      | some h => decide (ti.rets ≤ (sigRets h.sig).length)
      | none => true
    | .reg _ => P.funcs.all fun h => !declB g h.name ||
      decide ((regLocs h.sig).length ≠ (decU info.uses).length) ||
      decide (ti.rets ≤ (sigRets h.sig).length)
  | _ => true

theorem tryB_reg {P : Clif.Program} {g : Clif.Function} {vc : VCode}
    (h : allInsts vc (tryB P g) = true) {info : CallInfo} {ti : TryInfo} (hs : vc.TrySite info ti)
    {t : Nat} {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)}
    (hi : info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩) {h' : Clif.Function}
    (hh : h' ∈ P.funcs) (hdecl : DeclN g h'.name) (hl : (regLocs h'.sig).length = Lu.length) :
    ti.rets ≤ (sigRets h'.sig).length := by
  obtain ⟨b, vb, k, hb, hk⟩ := hs
  have := allInsts_sound h hb hk
  subst hi
  simp only [tryB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  have hdu : decU (retPairs Lu) = Lu := by
    simp [decU, retPairs, Function.comp_def]
  rcases this h' hh with (h1 | h1) | h1
  · rw [declB_of hdecl] at h1; cases h1
  · rw [hdu] at h1; exact absurd hl h1
  · exact h1

theorem tryB_sound {P : Clif.Program} {g : Clif.Function} {vc : VCode} (h : allInsts vc (tryB P g) = true)
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

/-- No `return_call`. -/
def linkFreeB (g : Clif.Function) : Bool :=
  g.blocks.all fun b => match b.term with | .returnCall .. => false | _ => true

theorem linkFreeB_sound {g : Clif.Function} (h : linkFreeB g = true) : Clif.LinkFree g := by
  intro b hb fn args he
  simp only [linkFreeB, List.all_eq_true] at h
  have := h b hb
  rw [he] at this; simp at this

/-- No `call_indirect`, `try_call_indirect`. -/
def indFreeB (g : Clif.Function) : Bool :=
  g.blocks.all fun b =>
    b.body.all (fun st => match st.inst with | .callIndirect .. => false | _ => true) &&
    (match b.term with | .tryCallIndirect .. => false | _ => true)

theorem indFreeB_sound {g : Clif.Function} (h : indFreeB g = true) : Clif.IndFree g := by
  intro b hb
  simp only [indFreeB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨fun st hst sig callee args he => ?_, fun callee args et he => ?_⟩
  · have := h1 st hst; rw [he] at this; simp at this
  · rw [he] at h2; simp at h2

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → b ∈ l.map (·.2)
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_pair {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hx
      cases h
      have : a = x := (beq_iff_eq.mp hx)
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_pair h)

/-- The call instructions of the laid-out code. -/
def callLine : Line → Bool
  | .ins (.bl _) _ => true
  | .ins (.blr _) _ => true
  | _ => false

/-- `ra` is outside the code of `a` (whose words fit the address space). -/
def outside (ra : BitVec 64) (a : Art) : Bool :=
  decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64) &&
    (decide (ra.toNat < a.base.toNat) || decide (a.base.toNat + 4 * a.fb.words.size ≤ ra.toNat))

theorem outside_sound {ra : BitVec 64} {a : Art} (h : outside ra a = true) :
    ∀ k < a.fb.words.size, ra ≠ a.base + BitVec.ofNat 64 (4 * k) := by
  intro k hk e
  simp only [outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨hfit, hr⟩ := h
  have hb := a.base.isLt
  have : ra.toNat = a.base.toNat + 4 * k := by
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  omega

/-- The return address of every call of `a` (the code of `g`) is outside the code of every other
function of the table. -/
def raCallB (T : List (Clif.Function × Art)) (g : Clif.Function) (a : Art) : Bool :=
  let ls := a.fa.lines.toList
  (List.range a.fa.lines.size).all fun j =>
    match a.fa.lines[j]? with
    | some l => !callLine l || T.all fun e => e.1.name == g.name ||
        outside (a.base + BitVec.ofNat 64 (lineOffset ls j) + 4) e.2
    | none => true

theorem raCallB_sound {T : List (Clif.Function × Art)} {g : Clif.Function} {a : Art}
    (h : raCallB T g a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) :
    ∀ e ∈ T, e.1.name ≠ g.name → ∀ k < e.2.fb.words.size,
      pc + 4 ≠ e.2.base + BitVec.ofNat 64 (4 * k) := by
  obtain ⟨j, i, t, hj, hi, rfl⟩ := hpc
  intro e he hne k hk
  have hj' : a.fa.lines[j]? = some (.ins i t) := by simpa using hj
  have hjl : j < a.fa.lines.size := (Array.getElem?_eq_some_iff.1 hj').1
  simp only [raCallB, List.all_eq_true, List.mem_range] at h
  have := h j hjl
  rw [hj'] at this
  have hc : callLine (.ins i t) = true := by
    rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at this
  exact outside_sound ((this e he).resolve_left hne) k hk

def raStarB (T : List (Clif.Function × Art)) (ra : BitVec 64) : Bool := T.all (outside ra ·.2)

/-- The image read back word by word. -/
def imgB (T : List (Clif.Function × Art)) : Bool :=
  let s := setMem Arm.ArmState.default (memT T)
  T.all fun e => (List.range e.2.fb.words.size).all fun k =>
    Arm.read_mem_bytes 4 (e.2.base + BitVec.ofNat 64 (4 * k)) s == e.2.fb.words[k]!

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

theorem imgCode_of {T : List (Clif.Function × Art)} (h : imgB T = true)
    {e : Clif.Function × Art} (he : e ∈ T) (t : Arm.ArmState)
    (ht : ∀ a, ImgT T a → t.mem a = memT T a) (k : Nat) (w : BitVec 32)
    (hw : e.2.fb.words[k]? = some w) :
    Arm.read_mem_bytes 4 (e.2.base + BitVec.ofNat 64 (4 * k)) t = w := by
  have hk : k < e.2.fb.words.size := (Array.getElem?_eq_some_iff.1 hw).1
  have hc := List.all_eq_true.1 (List.all_eq_true.1 h e he) k (List.mem_range.2 hk)
  simp only [beq_iff_eq] at hc
  rw [show e.2.fb.words[k]! = w by simp [Array.getElem!_eq_getD, hw]] at hc
  rw [← hc]
  refine rmb_congr 4 _ fun i hi => ?_
  have hm := wordsAt_mem (base := e.2.base) (k := 0) (j := k) (ws := e.2.fb.words.toList)
    (by simpa using hw)
  rw [Nat.zero_add] at hm
  refine ht _ ⟨e, he, ⟨_, hm, ?_⟩⟩
  rw [BitVec.add_comm _ (BitVec.ofNat 64 i), BitVec.add_sub_cancel]
  simp only [BitVec.toNat_ofNat]
  omega

/-- `g` is called in `P`: a function of `P` declares it. -/
def calleeB (P : Clif.Program) (g : Clif.Function) : Bool :=
  P.funcs.any fun g' => g'.externs.any fun e => e.2.name == g.name

/-- The slots of `g` fit in its compiled slot region (`LinkSys.Ok.slotFits`). -/
def slotFitsB (g : Clif.Function) (a : Art) : Bool :=
  g.slots.all fun p => match (slotLayout g.slots).1.lookup p.1 with
    | some off => decide (a.af.slotBase + off + p.2.size ≤ a.af.frameSize)
    | none => false

theorem slotFitsB_sound {g : Clif.Function} {a : Art} (h : slotFitsB g a = true) :
    ∀ p ∈ g.slots, ∃ off, (slotLayout g.slots).1.lookup p.1 = some off ∧
      a.af.slotBase + off + p.2.size ≤ a.af.frameSize := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  revert this
  cases (slotLayout g.slots).1.lookup p.1 with
  | none => simp
  | some off => exact fun h' => ⟨off, rfl, of_decide_eq_true h'⟩

/-- The scope of the indirect calls of `g` (`indScope`'s declarations, `indNoSym`, `indSig`),
with the CLIF image's symbols `S`. -/
def indB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  indFreeB g || ((indSigs g).all (fun s => !s.params.any (·.purpose == .sret)) &&
    P.funcs.all (fun h => !declB g h.name || (!h.sig.params.any (·.purpose == .sret) &&
      (match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false))) &&
    S g.name == none &&
    (Clif.Program.names P).all (fun n => n == g.name || S n == none ||
      g.externs.any (·.2.name == n)))

/-- Distinct names of `P` with an address have distinct addresses (`Clif.SymInj`). -/
def symNamesB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  let ns := (Clif.Program.names P).filter fun n => (S n).isSome
  ns.all fun a => ns.all fun b => S a != S b || a == b

/-- The machine's address of every function of `P` is no other symbol's (`Ok.symInj`): it is
a nonzero 64-bit address (names without one resolve to `0`) that no other link-map entry has. -/
def symInjB (I : LinkInput) (P : Clif.Program) : Bool :=
  P.funcs.all fun h => let a := I.addrOf h.name
    decide (a < 2 ^ 64) && a != 0 && I.addrs.all fun e => e.1 == h.name || e.2 % 2 ^ 64 != a

/-- The CLIF image's symbols are at their link-map addresses (`Ok.symOk`). -/
def symOkB (I : LinkInput) : Bool := I.syms.all fun e => I.addrOf e.1 == e.2

/-- With an outgoing-argument area and an indirect call in `P`, the functions with an address
have no stack slots (`Ok.addrSlots`). -/
def addrSlotsB (P : Clif.Program) (T : List (Clif.Function × Art)) (S : String → Option Nat) :
    Bool :=
  !(T.any (fun e => (RAFrame.compute e.2.vcp e.2.rf).intBase != 0) && P.funcs.any (!indFreeB ·)) ||
    P.funcs.all fun h => (S h.name).isNone || h.slots.isEmpty

/-- **The per-function checks** of `g` (pipeline result `r`), named by the premise of
`LinkSys.Ok` (or of `Compiled`/`InSubset`) they discharge. -/
def chks (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  [("compiled: pipeline", r.toBool),
   ("compiled: lowerCheck", lowerCheck g a.vc),
   ("compiled: prepCheck", prepCheck a.vc a.vcp),
   ("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("tryRets/blrTry", allInsts a.vcp (tryB P g)),
   ("sretRets", allInsts a.vc (retsB g)),
   ("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("argRegs: distinct", decide (regLocs g.sig).Nodup),
   ("argRegs: argument registers", (regLocs g.sig).all (·.isArgReg)),
   ("argRegs: width ≤ 64", g.sig.params.all (fun p => decide (p.ty.width ≤ 64))),
   ("calleeFrame/slotFits",
     !calleeB P g || ((!g.slots.isEmpty || fr.size == a.af.frameSize) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOk P g))),
   ("declSig", g.externs.all fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
   ("entryRegs", entryB g a.vcp),
   ("fits", decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64)),
   ("raCall/raBlr", raCallB T g a),
   ("depth", decide (frameDrop a.af ≤ I.D)),
   ("free (no return_call)", linkFreeB g),
   ("subset: clif-subset-v2 E", Compile.functionE g),
   ("subset: no direct self-call", g.externs.all (fun e => e.2.name != g.name)),
   ("subset: ABI signatures", sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)),
   ("subset: indirect-call signatures", indSigsOk g),
   ("indScope/indNoSym/indSig", indB P (fun n => I.syms.lookup n) g)]

/-- The checks of the whole program (`P`, the layout, the symbols). -/
def globalChks (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) :
    List (String × Bool) :=
  let S := fun n => I.syms.lookup n
  [("names: distinct", decide (P.funcs.map (·.name)).Nodup),
   ("imgCode: the image reads back", imgB T),
   ("raStar", raStarB T (BitVec.ofNat 64 I.raStar)),
   ("symInj", symInjB I P),
   ("symOk", symOkB I),
   ("indScope: SymInj", P.funcs.all indFreeB || symNamesB P S),
   ("addrSlots", addrSlotsB P T S)]

def okR (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  (globalChks I P T).all (·.2) && R.all fun e => (chks I P T e.1 e.2).all (·.2)

/-- **The checker**: every premise of `LinkSys.Ok` about the program and its layout. -/
def okB (I : LinkInput) : Bool := okR I I.results

/-- The names of the failing checks. -/
def bad (cs : List (String × Bool)) : List String := (cs.filter (!·.2)).map (·.1)

/-- **The diagnostic version of `okR`**: the failing global checks, then per function (by name)
the failing checks (and the pipeline's error). `okR I R = true` if it is empty (`diagR_nil`). -/
def diagR (I : LinkInput) (R : Res) : List (String × List String) :=
  let P := progOf R
  let T := tabOf R
  let gl := bad (globalChks I P T)
  let fs := R.filterMap fun e =>
    match bad (chks I P T e.1 e.2) with
    | [] => none
    | b => some (e.1.name, b ++ (match e.2 with | .error m => [m] | .ok _ => []))
  (if gl.isEmpty then [] else [("(program)", gl)]) ++ fs

/-- **The diagnostic version of `okB`** (`diag_nil`). -/
def diag (I : LinkInput) : List (String × List String) := diagR I I.results

/-! ## Soundness -/

theorem name_inj : ∀ {l : List Clif.Function}, (l.map (·.name)).Nodup →
    ∀ {a b : Clif.Function}, a ∈ l → b ∈ l → a.name = b.name → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, hn, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (he ▸ List.mem_map_of_mem (f := (·.name)) hb') hn.1
    · exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.name)) ha') hn.1
    · exact name_inj hn.2 ha' hb' he

theorem results_spec {I : LinkInput} {e : Clif.Function × Except String Art}
    (he : e ∈ I.results) : ∃ k j, e.2 = pipe e.1 k (BitVec.ofNat 64 (I.addrOf e.1.name)) j := by
  obtain ⟨fi, -, rfl⟩ := List.mem_map.1 he
  exact ⟨_, _, rfl⟩

theorem artOf_spec {R : Res} (hn : ((progOf R).funcs.map (·.name)).Nodup) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : ∃ e ∈ R, e.1 = g ∧ artOf R g = getOk e.2 := by
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 hg
  have hf : (R.find? fun e => e.1.name == e0.1.name).isSome := by
    rw [List.find?_isSome]; exact ⟨e0, he0, by simp⟩
  obtain ⟨e, hfe⟩ := Option.isSome_iff_exists.1 hf
  have hmem := List.mem_of_find?_eq_some hfe
  have hname : e.1.name = e0.1.name := by simpa using List.find?_some hfe
  have heq : e.1 = e0.1 :=
    name_inj hn (List.mem_map_of_mem (f := (·.1)) hmem) (List.mem_map_of_mem (f := (·.1)) he0) hname
  refine ⟨e, hmem, heq, ?_⟩
  simp only [artOf, hfe]

theorem tab_mem {R : Res} (hn : ((progOf R).funcs.map (·.name)).Nodup) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : (g, artOf R g) ∈ tabOf R := by
  obtain ⟨e, he, rfl, ha⟩ := artOf_spec hn hg
  rw [ha]
  exact List.mem_map.2 ⟨e, he, rfl⟩

/-- What the checks give for a function `g` of `P` (`P`, `A`, `T` of the input's results). -/
structure Facts (I : LinkInput) (g : Clif.Function) (a : Art) : Prop where
  pipe : ∃ k j, pipe g k (BitVec.ofNat 64 (I.addrOf g.name)) j = .ok a
  lowerOk : lowerCheck g a.vc = true
  prepOk : prepCheck a.vc a.vcp = true
  check : checkAlloc a.vcp a.rf = .ok ()
  covered : FormsCovered ⟨a.fa.k, a.af.slotBase⟩
    a.vcp
  tries : allInsts a.vcp (tryB (progOf I.results) g) = true
  rets : allInsts a.vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, ((progOf I.results).func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute a.vcp a.rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB (progOf I.results) g = true → (g.slots = [] →
    (RAFrame.compute a.vcp a.rf).size =
      a.af.frameSize) ∧ slotFitsB g a = true
  sites : allInsts a.vcp (siteB (siteOk (progOf I.results) g)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf I.results).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf I.results) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  extName : ∀ e ∈ g.externs.map (·.2), e.name ≠ g.name
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB (progOf I.results) (fun n => I.syms.lookup n) g = true

theorem okB_global {I : LinkInput} (h : okB I = true) :
    ∀ c ∈ globalChks I (progOf I.results) (tabOf I.results), c.2 = true := by
  simp only [okB, okR, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okB_names {I : LinkInput} (h : okB I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup := by
  have := okB_global h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

theorem facts {I : LinkInput} (h : okB I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.results).funcs) : Facts I g (artOf I.results g) := by
  have hn := okB_names h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chks I (progOf I.results) (tabOf I.results) e.1 e.2, c.2 = true := by
    simp only [okB, okR, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h21 h22
  obtain ⟨k, j, hp⟩ := results_spec he
  refine ⟨⟨k, j, by rw [← hp]; exact getOk_eq h1⟩, h2, h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h6, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20, fun x hx => ?_,
    ⟨h22.1, h22.2⟩, h23, h24⟩
  · rcases h8 x hx with h | h
    · simp [hs] at h
    · exact h
  · rcases h12 with h | ⟨h', hfit⟩
    · simp [hc] at h
    · refine ⟨fun hs => ?_, hfit⟩
      rcases h' with h | h
      · simp [hs] at h
      · exact h
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 hx
    have := h14 _ hm
    simp only [hf, decide_eq_true_eq] at this
    exact this
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 hx
    simpa using h21 _ hm

theorem symNames_sound {P : Clif.Program} {S : String → Option Nat} (h : symNamesB P S = true) :
    Clif.SymInj P S := by
  intro a ha b hb x hxa hxb
  simp only [symNamesB, List.all_eq_true, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  rcases h a ⟨ha, by simp [hxa]⟩ b ⟨hb, by simp [hxb]⟩ with h' | h'
  · exact absurd (hxa.trans hxb.symm) h'
  · exact h'

theorem indFacts {I : LinkInput} (h : okB I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.results).funcs) (hnf : ¬ Clif.IndFree g) :
    (∀ sig ∈ indSigs g, sig.params.any (·.purpose == .sret) = false) ∧
    (∀ h ∈ (progOf I.results).funcs, DeclN g h.name → h.sig.params.any (·.purpose == .sret) = false ∧
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
    I.syms.lookup g.name = none ∧
    ∀ n ∈ Clif.Program.names (progOf I.results), n ≠ g.name → I.syms.lookup n ≠ none →
      n ∈ g.externs.map (·.2.name) := by
  have h := (facts h hg).ind
  simp only [indB, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact absurd (indFreeB_sound h) hnf
  refine ⟨fun sig hs => by simpa using h1 sig hs, fun h' hh hd => ?_, by simpa using h3,
    fun n hn hne hs => ?_⟩
  · have h2' := h2 h' hh
    rw [declB_of hd] at h2'
    revert h2'
    cases hs : h'.sig.params.any (·.purpose == .sret) <;>
      cases hb : sigParamBytes h'.sig <;> simp_all
  · have := h4 n hn
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
    rcases this with (e | e) | ⟨x, hx, hxn⟩
    · exact absurd e hne
    · exact absurd e hs
    · exact List.mem_map.mpr ⟨x, hx, hxn⟩

theorem addrOf_of_lookup {I : LinkInput} {n : String} {b : Nat} (h : I.addrs.lookup n = some b) :
    I.addrOf n = b := by
  simp [LinkInput.addrOf, h]

theorem addrOf_cases (I : LinkInput) (n : String) :
    I.addrOf n = 0 ∨ (n, I.addrOf n) ∈ I.addrs := by
  unfold LinkInput.addrOf
  cases hl : I.addrs.lookup n with
  | none => exact .inl rfl
  | some b => exact .inr (by simpa using lookup_pair hl)

theorem symAddr_zero (I : LinkInput) (n : String) :
    I.symAddr n 0 = BitVec.ofNat 64 (I.addrOf n) := by
  simp [LinkInput.symAddr]

/-- **Soundness of the checker**: with the base environment's premises (`BaseOk`) and `F`
containing the code, the linked system of an input that passes `okB` satisfies every premise of
`backend_correct_program`'s `LinkSys.Ok`. -/
theorem okB_sound {I : LinkInput} (hI : okB I = true) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInput I B F)) (hF : ∀ a, (LinkSys.ofInput I B F).Img a → F a) :
    (LinkSys.ofInput I B F).Ok := by
  have hn := okB_names hI
  have hgl := okB_global hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, hsymn, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf I.results).funcs) => facts hI hg
  have site : ∀ g ∈ (progOf I.results).funcs, ∀ info h,
      (LinkSys.ofInput I B F).ProgSite g info h →
      h ∈ (progOf I.results).funcs ∧ h.name ≠ g.name ∧ calleeB (progOf I.results) h = true ∧
        ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length = (List.range (sigRets h.sig).length).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    have hf' : (progOf I.results).func? n = some h := hf
    obtain ⟨hne, ⟨e, he, hen⟩, Lu, Ld, heq, h1, h2⟩ :=
      siteOk_sound (site_sound (fa hg).sites hs) hd hf'
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, hne, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, List.any_eq_true, beq_iff_eq]
    exact ⟨g, hg, e, he, by rw [hen, hname]⟩
  have hcal : ∀ g ∈ (progOf I.results).funcs, ∀ h, (LinkSys.ofInput I B F).Callee g h →
      (h.slots = [] → (RAFrame.compute (artOf I.results h).vcp (artOf I.results h).rf).size =
        (artOf I.results h).af.frameSize) ∧ slotFitsB h (artOf I.results h) = true := by
    intro g hg h hh
    have hc : calleeB (progOf I.results) h = true ∧ h ∈ (progOf I.results).funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, he, hf⟩
      · obtain ⟨hh', -, hc, -⟩ := site g hg info h hs
        exact ⟨hc, hh'⟩
      · obtain ⟨hh', hname⟩ := Clif.Program.func?_some (p := progOf I.results) hf
        refine ⟨?_, hh'⟩
        obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
        simp only [calleeB, List.any_eq_true, beq_iff_eq]
        exact ⟨g, hg, (fn, e'), hm, hname.symm⟩
    exact (fa hc.2).callee hc.1
  have hpipe : ∀ g ∈ (progOf I.results).funcs,
      Compiled g (artOf I.results g).k (artOf I.results g).vc (artOf I.results g).vcp
        (artOf I.results g).rf (artOf I.results g).af (artOf I.results g).fa
        (artOf I.results g).fb ∧ (artOf I.results g).base = BitVec.ofNat 64 (I.addrOf g.name) := by
    intro g hg
    obtain ⟨k, j, hp⟩ := (fa hg).pipe
    obtain ⟨hl, hpr, ha, he, hla, -, hb⟩ := pipe_spec hp
    exact ⟨⟨hl, (fa hg).lowerOk, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩, hb⟩
  refine
    { names := hn
      free := fun g hg => (fa hg).free
      subset := fun g hg => ⟨?_, (fa hg).subsetE, ?_, ?_, (fa hg).abi, ?_⟩
      compiled := fun g hg => (hpipe g hg).1
      covered := fun g hg => (fa hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := hB.baseNoAlloc
      tryRets := fun g hg info ti h hs ⟨_, n, hd, hf⟩ => tryB_sound (fa hg).tries hs hd hf
      argRegs := fun g hg => ⟨(fa hg).nodup, (fa hg).argReg, (fa hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (fa hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2.2
      blrRegs := fun g hg info hs hreg =>
        blrOk_sound (siteOk_reg (site_sound (fa hg).sites hs) hreg)
      blrTry := fun g hg info ti hs t Lu Ld hi h hh hdecl hl =>
        tryB_reg (fa hg).tries hs hi hh hdecl hl
      raBlr := fun g hg info hs hreg h hh hdecl pc hpc k hk =>
        raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hdecl.2 k hk
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, (indFacts hI hg hnf).2.2.2⟩
      indNoSym := fun g hg hnf => (indFacts hI hg hnf).2.2.1
      indSig := fun g hg hnf => ⟨(indFacts hI hg hnf).1, (indFacts hI hg hnf).2.1⟩
      addrSlots := fun ⟨g, hg, hout⟩ ⟨g', hg', hind⟩ h hh hs => ?_
      symInj := fun h hh n hn => ?_
      declSig := fun g hg e he h hf => (fa hg).declSig e he h hf
      entryRegs := fun g hg r hr => entryB_sound (fa hg).entry hr
      fits := fun g hg => (fa hg).fits
      imgAddr := fun g hg a ha => ⟨_, tab_mem hn hg, ha⟩
      imgCode := fun g hg t ht k w hw => imgCode_of himg (tab_mem hn hg) t ht k w hw
      imgF := hF
      raCall := fun g hg info h hs pc hpc => ?_
      raStar := fun h hh k hk => ?_
      depth := fun g hg => (fa hg).depth
      symOk := fun n b hn' => ?_
      baseOs := hB.baseOs
      basePc := hB.basePc
      baseExt := hB.baseExt
      baseX := hB.baseX
      baseXI := hB.baseXI
      baseTls := hB.baseTls
      baseTry := hB.baseTry
      baseNI := hB.baseNI
      baseTlsNI := hB.baseTlsNI
      baseKeepsPlace := hB.baseKeepsPlace
      baseKeepsAllocs := hB.baseKeepsAllocs }
  · simp [LinkSys.ofInput, ofRes, Clif.Program.only, Clif.Program.func?]
  · intro b _ st _ fn args _ e he
    have hne := (fa hg).extName e (lookup_mem he)
    simp [LinkSys.ofInput, ofRes, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · intro b _ fn args et _ e he
    have hne := (fa hg).extName e (lookup_mem he)
    simp [LinkSys.ofInput, ofRes, Clif.Program.only, Clif.Program.func?, Ne.symm hne]
  · intro sig hs
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    exact outFitsB_sound ((fa hg).outFits _ hm hs) hl hp
  · simp only [Bool.or_eq_true, List.all_eq_true] at hsymn
    rcases hsymn with h | h
    · exact absurd (indFreeB_sound (h g hg)) hnf
    · exact symNames_sound h
  · simp only [addrSlotsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.any_eq_false, List.all_eq_true, Bool.not_eq_true, bne_iff_ne, ne_eq,
      Decidable.not_not, Bool.or_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at haddr
    rcases haddr with (h1 | h1) | h1
    · exact absurd (h1 _ (tab_mem hn hg)) hout
    · exact absurd (indFreeB_sound (by simpa using h1 g' hg')) hind
    · exact (h1 h hh).resolve_left hs
  · simp only [symInjB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq, Bool.or_eq_true, beq_iff_eq] at hinj
    obtain ⟨⟨hlt, h0⟩, hall⟩ := hinj h hh
    have hn' : I.symAddr h.name 0 = I.symAddr n 0 := hn
    rw [symAddr_zero, symAddr_zero] at hn'
    have e1 : (I.addrOf h.name) = (I.addrOf n) % 2 ^ 64 := by
      have := congrArg BitVec.toNat hn'
      simpa [Nat.mod_eq_of_lt hlt] using this
    by_cases hne : n = h.name
    · exact hne
    exfalso
    rcases addrOf_cases I n with hz | hm
    · rw [hz] at e1; exact h0 (by simpa using e1)
    · rcases hall _ hm with h' | h'
      · exact hne h'
      · exact h' e1.symm
  · obtain ⟨hh, hne, -⟩ := site g hg info h hs
    exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hne
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]

/-! ## The base premises are satisfiable -/

/-- **The closed base environment**: no extern outside the program has a semantics (CLIF:
`Clif.Env.empty`; machine: `call` undefined), a call outside the program continues at the next
instruction, TLS keeps the state, the TLSDESC flags are the world's. -/
def closedBase : BaseEnv where
  env := Clif.Env.empty
  call _ _ _ := none
  tp := 0
  tlsFlags _ s := Arm.read_pstate s
  hooks := ⟨fun _ s => Arm.w .PC (Arm.r .PC s + 4) s, fun _ _ s => s⟩

theorem closedBase_tlsNI {I : LinkInput} {R : Res} {F' : BitVec 64 → Prop}
    (F : BitVec 64 → Prop) : XTls F (ofRes I R closedBase F').Xb := by
  intro Z n w w' _ hsw
  have e : ∀ fl, Arm.r (.FLAG fl) w = Arm.r (.FLAG fl) w' := fun fl => hsw.1 _ (by simp [Masked])
  have h1 := e .N
  have h2 := e .Z
  have h3 := e .C
  have h4 := e .V
  simp only [Arm.r, Arm.read_base_flag] at h1 h2 h3 h4
  show Arm.read_pstate w = Arm.read_pstate w'
  apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption

/-- **Non-vacuity of `BaseOk`**: the closed base environment satisfies every base premise of
every input without `tls_value` (decidable: `hasTls`). With it the crate's theorem covers the
runs that call nothing outside the program (a call outside it is stuck in CLIF). -/
theorem baseOk_closed {I : LinkInput} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ (progOf I.results).funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInput I closedBase F) where
  baseNoAlloc := fun _ n gsem hn => by
    simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at hn
  keepSyms := fun _ n f h => by simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at h
  baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
      _ hsem => by simp [csem, LinkSys.ofInput, ofRes, closedBase] at hsem
  basePc := fun d s _ _ _ => by simp [LinkSys.ofInput, ofRes, closedBase, Arm.r_of_w_same]
  baseExt := fun d uses w outs w' _ hx => by simp [LinkSys.ofInput, ofRes, closedBase] at hx
  baseX := fun g hg F' slotOff out c => by
    intro ext _ gs sl cm w d uses args vals rvals cm' he
    simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at he
  baseXI := fun g hg F' slotOff out c sig _ n gsem sl cm w u args vals rvals cm' hgs => by
    simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at hgs
  baseTls := fun g hg ht => absurd ht (by simp [htls g hg])
  baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
    simp [csem, LinkSys.ofInput, ofRes, closedBase] at hsem
  baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
    simp [LinkSys.ofInput, ofRes, closedBase] at hx
  baseTlsNI := fun _ F' => closedBase_tlsNI F'
  baseKeepsPlace := fun _ n gsem hn => by
    simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at hn
  baseKeepsAllocs := fun _ n gsem hn => by
    simp [LinkSys.ofInput, ofRes, closedBase, Clif.Env.empty] at hn

/-! ## The crate's theorem -/

/-- `okB` and `diag` agree. -/
theorem bad_nil {cs : List (String × Bool)} (h : bad cs = []) : cs.all (·.2) = true := by
  simp only [bad, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  simp only [List.all_eq_true]
  intro c hc
  simpa using h c hc

theorem diagR_nil {I : LinkInput} {R : Res} (h : diagR I R = []) : okR I R = true := by
  unfold diagR at h
  rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff] at h
  obtain ⟨hg, hf⟩ := h
  simp only [okR, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun c hc => ?_, fun e he => List.all_eq_true.1 (bad_nil ?_)⟩
  · have : bad (globalChks I (progOf R) (tabOf R)) = [] := by
      revert hg
      split
      · rename_i hb; intro _; exact List.isEmpty_iff.1 hb
      · intro hb; cases hb
    exact List.all_eq_true.1 (bad_nil this) c hc
  · have := hf e he
    revert this
    cases hb : bad (chks I (progOf R) (tabOf R) e.1 e.2) with
    | nil => intro _; rfl
    | cons x xs => intro h; simp at h

theorem diag_nil {I : LinkInput} (h : diag I = []) : okB I = true := diagR_nil h

/-- **`backend_correct_program` for the function named `n` of the linked system `L`**, every
premise but `L.Ok`: for every entry of `n`, the linked machine refines the whole-program CLIF
run. -/
def ProgStmt (L : LinkSys) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s → StackAvail (L.K M) (L.A f).af s →
    L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a) →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs →
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs)

/-- **The crate's theorem for its function named `n`**: for every base environment `B` that
satisfies the base premises (`BaseOk`) and every `F` containing the code,
`backend_correct_program` holds for `n` in the linked system of the crate's input. -/
def CrateStmt (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInput I B F) →
    (∀ a, (LinkSys.ofInput I B F).Img a → F a) → ProgStmt (LinkSys.ofInput I B F) n

/-- **`backend_correct_program` for every function of an input that passes the checker.** -/
theorem crate_correct {I : LinkInput} (hI : okB I = true) (n : String) : CrateStmt I n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program _ (okB_sound hI hB hF) (Clif.Program.func?_some hf).1 M hent hres
      hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

/-- The program has a function named `n` (whatever the base environment). -/
theorem ofInput_func {I : LinkInput} {n : String} (h : ((progOf I.results).func? n).isSome = true)
    (B : BaseEnv) (F : BitVec 64 → Prop) : ∃ f, (LinkSys.ofInput I B F).P.func? n = some f :=
  Option.isSome_iff_exists.1 h

end E2E.LinkCheck
