import FV.E2E.LinkArm
import FV.Opt.Legalize128Pass
import FV.Backend.AllocReady

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
outside all code (`raStar`); the stack of one call level (`D`); `cargo fv`'s self-call aliases
(`aliases`: `(f__fvself, f)`, a function of the program with `f`'s body, its self-call naming
`f`, loaded at `f`'s address — one copy of the code, as the linker resolves the alias; the alias
has no symbol in the executable, so `addrs` gives it a fresh address no other symbol has); the
pipeline that compiles the functions (`fallback`: `false`, the checker's `pipe`, regalloc2's
allocation as given, which the checks then validate; `true`, the compiler's `pipeT`, which falls
back to the spill allocation when regalloc2's is rejected or not emittable — what `lean-backend`
and the Lean linker run, `LinkInput.results_fallback`). -/
structure LinkInput where
  funcs : List FnInput
  addrs : List (String × Nat)
  syms : List (String × Nat)
  raStar : Nat
  D : Nat
  aliases : List (String × String) := []
  fallback : Bool := false
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

/-- The load address of the function `n`: its link-map address, or its function's for an alias. -/
def LinkInput.baseOf (I : LinkInput) (n : String) : Nat := I.addrOf ((I.aliases.lookup n).getD n)

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

/-- regalloc2's answer for the prepared VCode `vcp`, read from `lean-regalloc`'s output (an
oracle: an error or a rejected allocation selects the spill allocation). -/
def raAnswer (vcp : VCode) (o : Lean.Json) : Except String RFunc := do
  let o ← parseRAOut o
  buildRFunc vcp o

/-- **The compiler's pipeline** on `f` (index `k` in its file, `lean-regalloc`'s output `o`)
loaded at `base`: `lowerFunction`, `prepare`, `lowerAllocReady` (regalloc2's allocation if
accepted and emittable, else the spill allocation), `emitFunc`, `layout`. The artifact's
allocation is the one lowered, `allocResult vcp (readyAnswer vcp ra)` (`lowerAllocReady_eq`). -/
def pipeT (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare vc
  let ra := raAnswer vcp o
  let af ← lowerAllocReady vcp ra
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, allocResult vcp (readyAnswer vcp ra), af, fa, fb, base⟩

theorem pipeT_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeT f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o)) ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
      a.k = k ∧ a.base = base := by
  unfold pipeT at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨rfl, h2, rfl, lowerAlloc_eq ((lowerAllocReady_eq _ _).symm.trans h3), h4, h5, rfl, rfl⟩

/-- **The entries of `R` are the pipeline's outputs**, loaded at their load addresses: what the
soundness of the checks (`okR_sound`) needs of the results, whichever allocator answer the
pipeline lowered (`results_ok`: the input's pipeline, `pipe` or `pipeT`). -/
def ResOk (I : LinkInput) (R : List (Clif.Function × Except String Art)) : Prop :=
  ∀ e ∈ R, ∀ a, e.2 = .ok a → lowerFunction e.1 = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧
    lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf e.1.name)

/-- The program's functions with their pipeline results (computed once by the checker). -/
abbrev Res := List (Clif.Function × Except String Art)

/-- The input's pipeline on `fi` (`fallback`: the compiler's `pipeT`, else the checker's
`pipe`), loaded at its load address. -/
def LinkInput.pipeOf (I : LinkInput) (fi : FnInput) : Except String Art :=
  cond I.fallback pipeT pipe fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)

/-- Every function of the input, compiled by the input's pipeline and loaded at its link-map
address. -/
def LinkInput.results (I : LinkInput) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeOf fi)

/-- Every function of the input, compiled by the compiler's pipeline and loaded at its link-map
address. -/
def LinkInput.resultsT (I : LinkInput) : Res :=
  I.funcs.map fun fi => let f := fi.func
    (f, pipeT f fi.k (BitVec.ofNat 64 (I.baseOf f.name)) (raJ fi.ra fi.j))

/-- **With `fallback`, the input's results are the compiler's** (`resultsT`): every theorem
stated for `I.results` (`okB`, `okB_sound`, `BinOk`, the binary theorems) is then about the code
the compiler emits. -/
theorem LinkInput.results_fallback {I : LinkInput} (h : I.fallback = true) :
    I.results = I.resultsT := by
  simp only [LinkInput.results, LinkInput.resultsT, LinkInput.pipeOf, h, Bool.cond_true]

/-- Without `fallback`, the input's results are the checker's pipeline `pipe`'s. -/
theorem LinkInput.results_raw {I : LinkInput} (h : I.fallback = false) :
    I.results = I.funcs.map fun fi => let f := fi.func
      (f, pipe f fi.k (BitVec.ofNat 64 (I.baseOf f.name)) (raJ fi.ra fi.j)) := by
  simp only [LinkInput.results, LinkInput.pipeOf, h, Bool.cond_false]

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

/-- The memory of a map of code words: the byte at `a` of the word at `a` rounded down to 4. -/
def memOfMap (m : Std.HashMap (BitVec 64) (BitVec 32)) (a : BitVec 64) : BitVec 8 :=
  match m[a &&& ~~~3#64]? with
  | some w => w.extractLsb' (8 * (a &&& 3#64).toNat) 8
  | none => 0

/-- **The code image**: the byte at `a` of the word at `a` rounded down to 4 bytes (the
checker's `imgB` reads every word back from it, so overlapping or misaligned code is rejected). -/
def memT (T : List (Clif.Function × Art)) : Arm.Memory := memOfMap (wordMap T)

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
keeping and the aliases of `Clif.IndScope` (needed only with indirect calls: names sharing an
address of no function of the program, one copy of code under several symbols, are one base
extern). They are not about the compiled
program, so no check decides them: they stay premises of the crate's theorem. -/
structure BaseOk (L : LinkSys) : Prop where
  baseNoAlloc : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    NoAllocEnv L.base
  keepSyms : (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → Opt.EnvKeepsSymbols L.base
  aliasSyms : (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → ∀ a ∈ L.P.names ++ L.base.names,
    ∀ b ∈ L.P.names ++ L.base.names, ∀ x, L.syms a = some x → L.syms b = some x →
      L.P.func? a = none → L.P.func? b = none → L.base.extern a = L.base.extern b
  baseOs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ F K G s0 Pc ctx, CallSoundCtlG F K G s0 Pc (callExec L.Hb) (csem F ctx L.Xb) (.call info) .next
  basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (L.Hb.call d s) = Arm.r .PC s + 4
  baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseX : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsOk L.base
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseXI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c,
    XCallsIndOk { L.base with sigOf := fun _ => none } (indSigs g)
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

/-- `g` declares `n`, including itself (`DeclN`). -/
def declB (g : Clif.Function) (n : String) : Bool :=
  g.externs.any (fun e => e.2.name == n)

theorem declB_of {g : Clif.Function} {n : String} (h : DeclN g n) : declB g n = true := by
  obtain ⟨e, he, hen⟩ := List.mem_map.mp h
  simp only [declB, List.any_eq_true, beq_iff_eq]
  exact ⟨e, he, hen⟩

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

/-- `g` may call `n` (an over-approximation of `LinkSys.MayCall`, with the CLIF image's symbols
`S`): declared, or with an address when `g` has indirect calls. -/
def mayB (S : String → Option Nat) (g : Clif.Function) (n : String) : Bool :=
  declB g n || (!indFreeB g && (S n).isSome)

theorem indFreeB_false {g : Clif.Function} (h : ¬ Clif.IndFree g) : indFreeB g = false := by
  cases hb : indFreeB g
  · rfl
  · exact absurd (indFreeB_sound hb) h

theorem mayB_of {L : LinkSys} {g : Clif.Function} {n : String} (h : L.MayCall g n) :
    mayB L.syms g n = true := by
  rcases h with hd | ⟨hnf, hs, -⟩
  · simp [mayB, declB_of hd]
  · simp only [mayB, indFreeB_false hnf, Bool.or_eq_true, Bool.not_false, Bool.true_and]
    exact .inr (by cases h' : L.syms n <;> simp_all)

/-- One of `g`'s indirect calls can enter `h` (`LinkSys.IndSigMatch`: its call-site signature
matches `h`'s, and as many results). -/
def indMatchB (g h : Clif.Function) : Bool :=
  (indSigs g).any fun s => decide (LinkSys.IndSigMatch s h) && h.sig.returns.length == s.returns.length

/-- `g` declares `n` non-colocated (`GotDecl`: a direct call of it goes through the GOT). -/
def gotDeclB (g : Clif.Function) (n : String) : Bool :=
  g.externs.any fun e => e.2.name == n && !e.2.colocated

theorem gotDeclB_of {g : Clif.Function} {n : String} (h : GotDecl g n) : gotDeclB g n = true := by
  obtain ⟨e, he, hn, hc⟩ := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  simp only [gotDeclB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  exact ⟨x, hx, hn, hc⟩

/-- `g` may enter `h` through an address (`LinkSys.IndTo`, with the CLIF image's symbols `S`). -/
def indToB (S : String → Option Nat) (g h : Clif.Function) : Bool :=
  mayB S g h.name && ((declB g h.name && gotDeclB g h.name) || indMatchB g h)

theorem indToB_of {L : LinkSys} {g h : Clif.Function} (hi : L.IndTo g h) :
    indToB L.syms g h = true := by
  obtain ⟨hmay, ⟨hd, hg⟩ | ⟨sig, hs, hm, hl⟩⟩ := hi
  · simp [indToB, mayB_of hmay, declB_of hd, gotDeclB_of hg]
  · simp only [indToB, mayB_of hmay, indMatchB, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact .inr ⟨sig, hs, hm, hl⟩

/-- A `blr` site: arguments in the parameter registers, of every function of `P` it may enter
(`LinkSys.BlrTo`: one the caller may enter through an address, `may`, and at a call through the
GOT, `got`, the GOT symbol's) with as many register parameters, and the results its defs hold from x0... -/
def blrOk (P : Clif.Program) (may : Clif.Function → Bool) (got : Nat → Option String) (info : CallInfo) :
    Bool :=
  match info.dest with
  | .reg (.vreg t .int) =>
    decide (info.uses = retPairs (decU info.uses)) &&
    decide (info.defs = callDefs (decD info.defs)) &&
    P.funcs.all fun h => !may h ||
      (match got t with | some n => h.name != n | none => false) ||
      decide ((regLocs h.sig).length ≠ (decU info.uses).length) ||
      (decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x))
  | _ => false

theorem blrOk_sound {P : Clif.Program} {may : Clif.Function → Bool} {got : Nat → Option String}
    {info : CallInfo} (h : blrOk P may got info = true) :
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ P.funcs, may h = true → (∀ n, got t = some n → h.name = n) →
        (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  unfold blrOk at h
  split at h
  · rename_i t hd
    simp only at hd
    subst hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨hu, hd⟩, hall⟩ := h
    refine ⟨t, decU us, decD ds, by rw [← hu, ← hd], fun h' hh hmay hgot hl => ?_⟩
    rcases hall h' hh with ((h1 | h1) | h1) | h1
    · rw [hmay] at h1; cases h1
    · revert h1
      cases hg : got t with
      | none => simp
      | some n => simp [hgot n hg]
    · exact absurd hl h1
    · exact h1
  · cases h

/-- A call site: a `bl` of a function `h` of `P` (other than `g`) that `g` declares, arguments in
`h`'s parameter registers, the results its defs hold from x0.. (then, at a `try_call`, the
exception payload registers); a `bl` of an extern outside `P` (the base's contract); or a `blr`
site (`blrOk`, with the GOT symbols of `vc`). -/
def siteOk (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool) (vc : VCode)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match P.func? n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => true
  | .reg _ => blrOk P may (gotOf vc) info

theorem siteOk_reg {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool} {vc : VCode}
    {info : CallInfo} (h : siteOk P g may vc info = true) (hd : ∀ n, info.dest ≠ .sym n) :
    blrOk P may (gotOf vc) info = true := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOk at h
  cases d with
  | reg r => exact h
  | sym n => exact absurd rfl (hd n)

theorem siteOk_sound {P : Clif.Program} {g : Clif.Function} {may : Clif.Function → Bool} {vc : VCode}
    {info : CallInfo} (h : siteOk P g may vc info = true) {n : String} {h' : Clif.Function} (hd : info.dest = .sym n)
    (hf : P.func? n = some h') :
    (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lu Ld,
      info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h'.sig ∧
      (Ld.map (·.1)).take (sigRets h'.sig).length =
        (List.range (min (sigRets h'.sig).length Ld.length)).map Reg.x := by
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  unfold siteOk at h
  simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hd, hu⟩, hdd⟩, h1⟩, h2⟩ := h
  exact ⟨hd, _, _, by rw [← hu, ← hdd], h1, h2⟩

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

/-- `LinkSys.RaOk` decided: the return address `pc + 4` is outside `ah`'s code, or `pc` is a
call of `ah`'s own code (one copy of code shared with the caller: `cargo fv`'s self-call alias)
and `pc + 4` is not its entry. -/
def raOkB (ah : Art) (pc : BitVec 64) : Bool :=
  outside (pc + 4) ah ||
  (pc + 4 != ah.base && (List.range ah.fa.lines.toList.length).any fun j =>
    match ah.fa.lines.toList[j]? with
    | some l => callLine l && pc == ah.base + BitVec.ofNat 64 (lineOffset ah.fa.lines.toList j)
    | none => false)

theorem raOkB_sound {ah : Art} {pc : BitVec 64} (h : raOkB ah pc = true) : RaOk ah pc := by
  simp only [raOkB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨hne, j, -, hl⟩
  · exact .inl (outside_sound h)
  · refine .inr ⟨?_, hne⟩
    revert hl
    cases e : ah.fa.lines.toList[j]? with
    | none => simp
    | some l =>
      intro hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      obtain ⟨hc, rfl⟩ := hl
      cases l with
      | ins i t =>
        cases i <;> simp only [callLine, Bool.false_eq_true] at hc
        · exact ⟨j, _, t, e, .inl ⟨_, rfl⟩, rfl⟩
        · exact ⟨j, _, t, e, .inr ⟨_, rfl⟩, rfl⟩
      | _ => simp [callLine] at hc

/-- The return address of every call of `a` (the code of `g`) is outside the code of every other
function of the table, or after a call of that function's own code (`raOkB`). -/
def raCallB (T : List (Clif.Function × Art)) (g : Clif.Function) (a : Art) : Bool :=
  let ls := a.fa.lines.toList
  (List.range a.fa.lines.size).all fun j =>
    match a.fa.lines[j]? with
    | some l => !callLine l || T.all fun e => e.1.name == g.name ||
        raOkB e.2 (a.base + BitVec.ofNat 64 (lineOffset ls j))
    | none => true

theorem raCallB_sound {T : List (Clif.Function × Art)} {g : Clif.Function} {a : Art}
    (h : raCallB T g a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) :
    ∀ e ∈ T, e.1.name ≠ g.name → RaOk e.2 pc := by
  obtain ⟨j, i, t, hj, hi, rfl⟩ := hpc
  intro e he hne
  have hj' : a.fa.lines[j]? = some (.ins i t) := by simpa using hj
  have hjl : j < a.fa.lines.size := (Array.getElem?_eq_some_iff.1 hj').1
  simp only [raCallB, List.all_eq_true, List.mem_range] at h
  have := h j hjl
  rw [hj'] at this
  have hc : callLine (.ins i t) = true := by
    rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at this
  exact raOkB_sound ((this e he).resolve_left hne)

/-- **A call of a function's own code returns after the call** (`RaOk`, for a function calling
itself through a pointer): its return address is within the laid-out words, which fit the address
space with an address outside them (`outside ra a`), so it is not the entry. -/
theorem raOk_self {a : Art} (hl : a.fa.layout = .ok a.fb) {ra : BitVec 64}
    (ho : outside ra a = true) {pc : BitVec 64} (hpc : CallPc a.fa a.base pc) : RaOk a pc := by
  refine .inr ⟨hpc, ?_⟩
  obtain ⟨j, i, t, hj, -, rfl⟩ := hpc
  obtain ⟨m, hm⟩ := FnAsm.layout_labelOffsets hl
  obtain ⟨hmod, w, -, hw⟩ := FnAsm.layout_word hl hm hj rfl
  have hwl := (Array.getElem?_eq_some_iff.1 hw).1
  simp only [outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at ho
  have hb := a.base.isLt
  have hr := ra.isLt
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (4 : BitVec 64).toNat = 4 from rfl] at h'
  omega

def raStarB (T : List (Clif.Function × Art)) (ra : BitVec 64) : Bool := T.all (outside ra ·.2)

/-- The image read back word by word. -/
def imgB (T : List (Clif.Function × Art)) : Bool :=
  -- the map once (`memT T` itself compiles to a function of the address that rebuilds it)
  let m := wordMap T
  let s := setMem Arm.ArmState.default (memOfMap m)
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
def calleeB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  P.funcs.any (fun g' => g'.externs.any fun e => e.2.name == g.name) ||
    ((S g.name).isSome && P.funcs.any (!indFreeB ·))

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

/-- One of `g`'s indirect calls can enter `h` in the per-function run (`LinkSys.Ok.indSig`): its
call-site signature matches `h`'s (`LinkSys.IndSigMatch`), or `g` declares `h` and the call has
`h`'s parameter types (`LinkSys.IndTyMatch`). -/
def indSigB (g h : Clif.Function) : Bool :=
  (indSigs g).any (fun s => decide (LinkSys.IndSigMatch s h)) ||
    (declB g h.name && (indSigs g).any (fun s => decide (LinkSys.IndTyMatch s h)))

/-- An indirect call of `g` with `h`'s parameter types and as many declared returns has as many
ABI returns (`sigRets`; `LinkSys.Ok.indSig`). -/
def indRetsB (g h : Clif.Function) : Bool :=
  (indSigs g).all fun s => !decide (LinkSys.IndTyMatch s h) ||
    h.sig.returns.length != s.returns.length || (sigRets h.sig).length == (sigRets s).length

/-- The scope of the indirect calls of `g` (`indScope`'s declarations, `indSig`), with the CLIF
image's symbols `S`: the functions `g` may call that one of its indirect calls can enter
(`indSigB`) take register arguments (an `sret` pointer in x8) and have as many ABI returns as the
indirect calls of their parameter types (`indRetsB`). -/
def indB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  indFreeB g || P.funcs.all (fun h => !mayB S g h.name || !indSigB g h ||
      ((match sigParamBytes h.sig with | .ok b => decide (b.length ≤ 8) | .error _ => false) &&
        indRetsB g h))

/-- The machine's address of every function of `P` is no other symbol's (`Ok.symInj`): it is
a nonzero 64-bit address (names without one resolve to `0`) that no other link-map entry has. -/
def symInjB (I : LinkInput) (P : Clif.Program) : Bool :=
  P.funcs.all fun h => let a := I.addrOf h.name
    decide (a < 2 ^ 64) && a != 0 && I.addrs.all fun e => e.1 == h.name || e.2 % 2 ^ 64 != a

/-- The CLIF image's symbols are at their link-map addresses (`Ok.symOk`). -/
def symOkB (I : LinkInput) : Bool := I.syms.all fun e => I.addrOf e.1 == e.2

/-- A function of `P` declares a function of `P` with stack slots: a program callee has slots
(`LinkSys.NeedSlots`, `declSlotsB_sound`). -/
def declSlotsB (P : Clif.Program) : Bool :=
  P.funcs.any fun g => g.externs.any fun e => match P.func? e.2.name with
    | some h => !h.slots.isEmpty
    | none => false

theorem declSlotsB_sound {P : Clif.Program} (h : declSlotsB P = true) :
    ∃ g ∈ P.funcs, ∃ e ∈ g.externs.map (·.2), ∃ h', P.func? e.name = some h' ∧ h'.slots ≠ [] := by
  simp only [declSlotsB, List.any_eq_true] at h
  obtain ⟨g, hg, e, he, hs⟩ := h
  refine ⟨g, hg, e.2, List.mem_map_of_mem he, ?_⟩
  revert hs
  cases P.func? e.2.name with
  | none => simp
  | some h' => exact fun hs => ⟨h', rfl, by simpa using hs⟩

/-- With an outgoing-argument area and an indirect call in `P`, the functions with an address
have no stack slots (`Ok.addrSlots`), unless a program callee has slots (`declSlotsB`: then
`NeedSlots` holds and `Ok.addrSlots` is vacuous). -/
def addrSlotsB (P : Clif.Program) (T : List (Clif.Function × Art)) (S : String → Option Nat) :
    Bool :=
  !(T.any (fun e => (RAFrame.compute e.2.vcp e.2.rf).intBase != 0) && P.funcs.any (!indFreeB ·)) ||
    P.funcs.all (fun h => (S h.name).isNone || h.slots.isEmpty) || declSlotsB P

/-- **The per-function checks of `g` that do not depend on the rest of the program** (pipeline
result `r`), named by the premise of `LinkSys.Ok` (or of `Compiled`/`InSubset`) they discharge.
They include the validators (`lowerCheck` dominates the checker's time). -/
def staticChks (I : LinkInput) (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: lowerCheck", lowerCheck g a.vc),
   ("compiled: prepCheck", prepCheck a.vc a.vcp),
   ("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("sretRets", allInsts a.vc (retsB g)),
   ("argRegs: distinct", decide (regLocs g.sig).Nodup),
   ("argRegs: argument registers", (regLocs g.sig).all (·.isArgReg)),
   ("argRegs: width ≤ 64", g.sig.params.all (fun p => decide (p.ty.width ≤ 64))),
   ("entryRegs", entryB g a.vcp),
   ("fits", decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64)),
   ("depth", decide (frameDrop a.af ≤ I.D)),
   ("free (no return_call)", linkFreeB g),
   ("subset: clif-subset-v2 E", Compile.functionE g),
   ("subset: ABI signatures", sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)),
   ("subset: indirect-call signatures", indSigsOk g)]

/-- **The per-function checks of `g` against the program** `P` (its compiled table `T`). -/
def linkChks (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let may := indToB (fun n => I.syms.lookup n) g
  [("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !calleeB P (fun n => I.syms.lookup n) g || ((!g.slots.isEmpty || fr.size == a.af.frameSize) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOk P g may a.vcp))),
   ("declSig", g.externs.all fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
   ("raCall/raBlr", raCallB T g a),
   ("indScope/indSig", indB P (fun n => I.syms.lookup n) g)]

/-- **The per-function checks** of `g`. -/
def chks (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  staticChks I g r ++ linkChks I P T g r

/-- The checks of the whole program (`P`, the layout, the symbols). -/
def globalChks (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art)) :
    List (String × Bool) :=
  let S := fun n => I.syms.lookup n
  [("names: distinct", decide (P.funcs.map (·.name)).Nodup),
   ("imgCode: the image reads back", imgB T),
   ("raStar", raStarB T (BitVec.ofNat 64 I.raStar)),
   ("symInj", symInjB I P),
   ("symOk", symOkB I),
   ("addrSlots", addrSlotsB P T S)]

def okR (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  (globalChks I P T).all (·.2) && R.all fun e => (chks I P T e.1 e.2).all (·.2)

/-- **The checker**: every premise of `LinkSys.Ok` about the program and its layout, checked on
the input's results (`okB_fallback`: with `fallback`, on the compiler's own output). -/
def okB (I : LinkInput) : Bool := okR I I.results

/-- With `fallback`, `okB` is `okR` of the compiler's results `resultsT`: the same checks, on the
code the compiler emits. -/
theorem okB_fallback {I : LinkInput} (h : I.fallback = true) : okB I = okR I I.resultsT := by
  rw [okB, LinkInput.results_fallback h]

/-- The checks of the program (`globalChks`). -/
def globalB (I : LinkInput) : Bool :=
  let R := I.results
  (globalChks I (progOf R) (tabOf R)).all (·.2)

/-- The per-function checks (`chks`: `staticChks ++ linkChks`) of the functions `fs` (a slice of
the input's) against the input's program. A crate's proof decides `okB` by one `native_decide`
per slice, in separate modules that Lake builds in parallel (`okB_of`, `fnsB_append`). -/
def fnsB (I : LinkInput) (fs : List FnInput) : Bool :=
  let R := I.results
  let P := progOf R
  let T := tabOf R
  fs.all fun fi => (chks I P T fi.func (I.pipeOf fi)).all (·.2)

theorem fnsB_append (I : LinkInput) (l₁ l₂ : List FnInput) :
    fnsB I (l₁ ++ l₂) = (fnsB I l₁ && fnsB I l₂) := by
  simp only [fnsB, List.all_append]

/-- `okB` from its parts: `globalB` and `fnsB` of all the functions. -/
theorem okB_of {I : LinkInput} (hg : globalB I = true) (hf : fnsB I I.funcs = true) :
    okB I = true := by
  simp only [okB, okR, Bool.and_eq_true]
  refine ⟨hg, ?_⟩
  simp only [fnsB] at hf
  simp only [LinkInput.results, List.all_map]
  exact hf

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
    (he : e ∈ I.results) :
    ∃ k j, e.2 = cond I.fallback pipeT pipe e.1 k (BitVec.ofNat 64 (I.baseOf e.1.name)) j := by
  obtain ⟨fi, -, rfl⟩ := List.mem_map.1 he
  exact ⟨_, _, rfl⟩

/-- The input's results are the pipeline's outputs (`ResOk`). -/
theorem results_ok (I : LinkInput) : ResOk I I.results := by
  intro e he a ha
  obtain ⟨k, j, hp⟩ := results_spec he
  cases hfb : I.fallback <;> rw [hfb] at hp <;> rw [hp] at ha
  · obtain ⟨hl, hpr, hlr, hem, hla, -, hb⟩ := pipe_spec ha
    exact ⟨hl, hpr, hlr, hem, hla, hb⟩
  · obtain ⟨hl, hpr, -, hlr, hem, hla, -, hb⟩ := pipeT_spec ha
    exact ⟨hl, hpr, hlr, hem, hla, hb⟩

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

/-- What the checks give for a function `g` of `P` (`P`, `A`, `T` of the results `R`). -/
structure Facts (I : LinkInput) (R : Res) (g : Clif.Function) (a : Art) : Prop where
  pipe : lowerFunction g = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : lowerCheck g a.vc = true
  prepOk : prepCheck a.vc a.vcp = true
  check : checkAlloc a.vcp a.rf = .ok ()
  covered : FormsCovered ⟨a.fa.k, a.af.slotBase⟩
    a.vcp
  rets : allInsts a.vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, ((progOf R).func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute a.vcp a.rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB (progOf R) (fun n => I.syms.lookup n) g = true → (g.slots = [] →
    (RAFrame.compute a.vcp a.rf).size =
      a.af.frameSize) ∧ slotFitsB g a = true
  sites : allInsts a.vcp (siteB (siteOk (progOf R) g
    (indToB (fun n => I.syms.lookup n) g) a.vcp)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB (progOf R) (fun n => I.syms.lookup n) g = true

theorem okR_global {I : LinkInput} {R : Res} (h : okR I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okR, chks, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okR_names {I : LinkInput} {R : Res} (h : okR I R = true) :
    ((progOf R).funcs.map (·.name)).Nodup := by
  have := okR_global h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

theorem okB_global {I : LinkInput} (h : okB I = true) :
    ∀ c ∈ globalChks I (progOf I.results) (tabOf I.results), c.2 = true :=
  okR_global h

theorem okB_names {I : LinkInput} (h : okB I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup :=
  okR_names h

theorem factsR {I : LinkInput} {R : Res} (hR : ResOk I R) (h : okR I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : Facts I R g (artOf R g) := by
  have hn := okR_names h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chks I (progOf R) (tabOf R) e.1 e.2, c.2 = true := by
    simp only [okR, chks, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chks, staticChks, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h9, h10, h11, h15, h16, h18, h19, h20, h22, h23, h8,
    h12, h13, h14, h17, h24⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h22
  refine ⟨hR e he _ (getOk_eq h1), h2, h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20,
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

/-- What `okB` gives for a function `g` of the input's program (`factsR` of the checker's
results). -/
theorem facts {I : LinkInput} (h : okB I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.results).funcs) : Facts I I.results g (artOf I.results g) :=
  factsR (results_ok I) h hg

theorem indRetsB_sound {g h : Clif.Function} (hr : indRetsB g h = true) :
    ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
      (sigRets h.sig).length = (sigRets sig).length := by
  intro sig hs hm hl
  have := List.all_eq_true.mp hr sig hs
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq,
    beq_iff_eq] at this
  rcases this with (h1 | h1) | h1
  · exact absurd hm h1
  · exact absurd hl h1
  · exact h1

theorem indFactsR {I : LinkInput} {R : Res} (hR : ResOk I R) (h : okR I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length := by
  have h := (factsR hR h hg).ind
  simp only [indB, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with h | h2
  · exact absurd (indFreeB_sound h) hnf
  intro h' hh hd hm
  have hany : indSigB g h' = true := by
    simp only [indSigB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    rcases hm with ⟨sig, hs, hm⟩ | ⟨hdn, sig, hs, hm⟩
    · exact .inl ⟨sig, hs, hm⟩
    · exact .inr ⟨declB_of hdn, sig, hs, hm⟩
  have h2' := h2 h' hh
  simp only [Bool.and_eq_true] at h2'
  rw [hd, hany] at h2'
  rcases h2' with (e | e) | ⟨hb8, hr⟩
  · cases e
  · cases e
  refine ⟨?_, indRetsB_sound hr⟩
  revert hb8
  cases hb : sigParamBytes h'.sig <;> simp

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

/-- **Soundness of the checks** for results `R` that are the pipeline's outputs (`ResOk`): with
the base environment's premises (`BaseOk`) and `F` containing the code, the linked system of
results that pass `okR` satisfies every premise of `backend_correct_program`'s `LinkSys.Ok`. -/
theorem okR_sound {I : LinkInput} {R : Res} (hR : ResOk I R) (hI : okR I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    (ofRes I R B F).Ok := by
  have hn := okR_names hI
  have hgl := okR_global hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf R).funcs) => factsR hR hI hg
  have site : ∀ g ∈ (progOf R).funcs, ∀ info h,
      (ofRes I R B F).ProgSite g info h →
      h ∈ (progOf R).funcs ∧
        calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧
        ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    have hf' : (progOf R).func? n = some h := hf
    obtain ⟨⟨e, he, hen⟩, Lu, Ld, heq, h1, h2⟩ :=
      siteOk_sound (site_sound (fa hg).sites hs) hd hf'
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inl ⟨g, hg, e, he, by rw [hen, hname]⟩
  have hcal : ∀ g ∈ (progOf R).funcs, ∀ h, (ofRes I R B F).Callee g h →
      (h.slots = [] → (RAFrame.compute (artOf R h).vcp (artOf R h).rf).size =
        (artOf R h).af.frameSize) ∧ slotFitsB h (artOf R h) = true := by
    intro g hg h hh
    have hc : calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧
        h ∈ (progOf R).funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, he, hf⟩ | ⟨hh', hmay⟩
      · obtain ⟨hh', hc, -⟩ := site g hg info h hs
        exact ⟨hc, hh'⟩
      · obtain ⟨hh', hname⟩ := Clif.Program.func?_some (p := progOf R) hf
        refine ⟨?_, hh'⟩
        obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        exact .inl ⟨g, hg, (fn, e'), hm, hname.symm⟩
      · refine ⟨?_, hh'⟩
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true,
          Bool.not_eq_true']
        rcases hmay with hm | ⟨hnf, hs, -⟩
        · obtain ⟨⟨fn, e'⟩, he, hen⟩ := List.mem_map.1 hm
          exact .inl ⟨g, hg, (fn, e'), he, hen⟩
        · refine .inr ⟨?_, g, hg, indFreeB_false hnf⟩
          show (I.syms.lookup h.name).isSome = true
          cases h' : I.syms.lookup h.name
          · exact absurd h' hs
          · rfl
    exact (fa hc.2).callee hc.1
  have hpipe : ∀ g ∈ (progOf R).funcs,
      Compiled g (artOf R g).k (artOf R g).vc (artOf R g).vcp
        (artOf R g).rf (artOf R g).af (artOf R g).fa
        (artOf R g).fb ∧ (artOf R g).base = BitVec.ofNat 64 (I.baseOf g.name) := by
    intro g hg
    obtain ⟨hl, hpr, ha, he, hla, hb⟩ := (fa hg).pipe
    exact ⟨⟨hl, (fa hg).lowerOk, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩, hb⟩
  refine
    { names := hn
      free := fun g hg => (fa hg).free
      subset := fun g hg => ⟨(fa hg).subsetE, ?_, ?_, (fa hg).abi, ?_⟩
      compiled := fun g hg => (hpipe g hg).1
      covered := fun g hg => (fa hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := hB.baseNoAlloc
      argRegs := fun g hg => ⟨(fa hg).nodup, (fa hg).argReg, (fa hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (fa hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2
      blrRegs := fun g hg info hs hreg => by
        obtain ⟨t, Lu, Ld, heq, hall⟩ := blrOk_sound (siteOk_reg (site_sound (fa hg).sites hs) hreg)
        exact ⟨t, Lu, Ld, heq, fun h hh hb hl =>
          hall h hh (indToB_of hb.1) (fun n hn => (hb.2 n (gotOf_sound hn)).symm) hl⟩
      raBlr := fun g hg info hs hreg h hh hmay pc hpc => by
        by_cases hhg : h.name = g.name
        · rw [Clif.name_inj hn hh hg hhg]
          exact raOk_self (hpipe g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
        · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, hB.aliasSyms ⟨g, hg, hnf⟩⟩
      indSig := fun g hg hnf h hh hmay hm => indFactsR hR hI hg hnf h hh (mayB_of hmay) hm
      addrSlots := fun hN ⟨g, hg, hout⟩ ⟨g', hg', hind⟩ h hh hs => ?_
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
  · intro b _ st _ fn args _ e he
    exact Clif.Program.bare_func? _ _
  · intro b _ fn args et _ e he
    exact Clif.Program.bare_func? _ _
  · intro sig hs
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    exact outFitsB_sound ((fa hg).outFits _ hm hs) hl hp
  · -- the functions of `P` have distinct addresses: their link-map addresses (`symOk`), which
    -- no other link-map entry has (`symInj`)
    intro a ha b hb x hxa hxb
    obtain ⟨g', -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hb
    simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have ea : I.addrOf g'.name = x := hsymok _ (lookup_pair hxa)
    have eb : I.addrOf h'.name = x := hsymok _ (lookup_pair hxb)
    simp only [symInjB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq, Bool.or_eq_true, beq_iff_eq] at hinj
    obtain ⟨⟨hlt, h0⟩, hall⟩ := hinj h' hh'
    rcases addrOf_cases I g'.name with hz | hm
    · exact absurd (eb.trans (ea.symm.trans hz)) h0
    · rcases hall _ hm with e | e
      · exact e
      · exact absurd (by rw [ea, ← eb, Nat.mod_eq_of_lt hlt]) e
  · simp only [addrSlotsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.any_eq_false, List.all_eq_true, Bool.not_eq_true, bne_iff_ne, ne_eq,
      Decidable.not_not, Bool.or_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at haddr
    rcases haddr with ((h1 | h1) | h1) | h1
    · exact absurd (h1 _ (tab_mem hn hg)) hout
    · exact absurd (indFreeB_sound (by simpa using h1 g' hg')) hind
    · exact (h1 h hh).resolve_left hs
    · obtain ⟨g0, hg0, e, he, h0, hf, hs0⟩ := declSlotsB_sound h1
      exact absurd ⟨g0, hg0, h0, .inr (.inl ⟨e, he, hf⟩), hs0⟩ hN
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
  · obtain ⟨hh, -⟩ := site g hg info h hs
    by_cases hhg : h.name = g.name
    · rw [Clif.name_inj hn hh hg hhg]
      exact raOk_self (hpipe g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
    · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]

/-- **Soundness of the checker**: with the base environment's premises (`BaseOk`) and `F`
containing the code, the linked system of an input that passes `okB` satisfies every premise of
`backend_correct_program`'s `LinkSys.Ok`. -/
theorem okB_sound {I : LinkInput} (hI : okB I = true) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInput I B F)) (hF : ∀ a, (LinkSys.ofInput I B F).Img a → F a) :
    (LinkSys.ofInput I B F).Ok :=
  okR_sound (results_ok I) hI hB hF

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
the linked system of any results `R` without `tls_value` (decidable: `hasTls`). With it the
crate's theorem covers the runs that call nothing outside the program (a call outside it is
stuck in CLIF). -/
theorem baseOk_closedR {I : LinkInput} {R : Res} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ (progOf R).funcs, hasTls g = false) :
    BaseOk (ofRes I R closedBase F) where
  baseNoAlloc := fun _ n gsem hn => by
    simp [ofRes, closedBase, Clif.Env.empty] at hn
  keepSyms := fun _ n f h => by simp [ofRes, closedBase, Clif.Env.empty] at h
  aliasSyms := fun _ _ _ _ _ _ _ _ _ _ => by simp [ofRes, closedBase, Clif.Env.empty]
  baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
      _ hsem => by simp [csem, ofRes, closedBase] at hsem
  basePc := fun d s _ _ _ => by simp [ofRes, closedBase, Arm.r_of_w_same]
  baseExt := fun d uses w outs w' _ hx => by simp [ofRes, closedBase] at hx
  baseX := fun g hg F' slotOff out c => by
    intro ext _ gs sl cm w d uses args vals rvals cm' he
    simp [ofRes, closedBase, Clif.Env.empty] at he
  baseXI := fun g hg F' slotOff out c sig _ n gsem sl cm w u args vals rvals cm' hgs => by
    simp [ofRes, closedBase, Clif.Env.empty] at hgs
  baseTls := fun g hg ht => absurd ht (by simp [htls g hg])
  baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
    simp [csem, ofRes, closedBase] at hsem
  baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
    simp [ofRes, closedBase] at hx
  baseTlsNI := fun _ F' => closedBase_tlsNI F'
  baseKeepsPlace := fun _ n gsem hn => by
    simp [ofRes, closedBase, Clif.Env.empty] at hn
  baseKeepsAllocs := fun _ n gsem hn => by
    simp [ofRes, closedBase, Clif.Env.empty] at hn

/-- **Non-vacuity of `BaseOk`** for the linked system of an input (`baseOk_closedR`). -/
theorem baseOk_closed {I : LinkInput} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ (progOf I.results).funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInput I closedBase F) :=
  baseOk_closedR htls

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
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
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
