import FV.Opt.Proof.LegalComplete
import FV.Opt.Legalize128Pre

/-!
# The decidable `Pre` of the validator's completeness (S6)

`preB_iff : preB f = true ↔ Pre f`: the preconditions of `Opt.Legal.Complete.check_complete`
are decided on `f` alone (`Opt.Legalize128.preB`, `FV/Opt/Legalize128Pre.lean`), so the runtime
`Opt.Legal.check` is provably redundant on every function with `preB f = true`
(`check_complete_of_preB`); likewise `preBW_iff`/`checkW_complete_of_preBW` for `PreW` and
`Opt.Legal.checkW`. `legalOkB_cases`: the source domain of one function is the identity (no
`i128`) or `Pre` with a successful legalisation.
-/

namespace Opt.Legal.Complete

open Clif Opt.Legalize128

/-- **`PreW` is decidable**: `preBW` decides it. -/
theorem preBW_iff {f : Function} : preBW f = true ↔ PreW f := by
  constructor
  · intro h
    simp only [preBW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hm, hd⟩, hi⟩, hs⟩ := h
    refine ⟨hm, hd, fun v hv => by simpa using hi v hv, ?_⟩
    intro b hb s hs' x hx hr
    exact (by simpa using hs b hb s hs' x hx : x ∉ s.results) hr
  · intro hp
    simp only [preBW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨hp.mentions, hp.defs⟩, fun v hv => by simpa using hp.ids v hv⟩, ?_⟩
    intro b hb s hs x hx
    simpa using hp.noSelf b hb s hs x hx

/-- **`Pre` is decidable**: `preB` decides it. -/
theorem preB_iff {f : Function} : preB f = true ↔ Pre f := by
  constructor
  · intro h
    simp only [preB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hm, hd⟩, hi⟩, hs⟩, hc⟩, ht⟩ := h
    refine ⟨hm, hd, fun v hv => by simpa using hi v hv, ?_, ?_, ?_⟩
    · intro b hb s hs' x hx hr
      exact (by simpa using hs b hb s hs' x hx : x ∉ s.results) hr
    · intro b hb s hs' sig callee args hi' d hd'
      simpa [hi', hd'] using hc b hb s hs'
    · intro b hb c args et he
      have := ht b hb
      simp only [he] at this
      exact Bool.false_ne_true this
  · intro hp
    simp only [preB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨hp.mentions, hp.defs⟩, fun v hv => by simpa using hp.ids v hv⟩, ?_⟩, ?_⟩, ?_⟩
    · intro b hb s hs x hx
      simpa using hp.noSelf b hb s hs x hx
    · intro b hb s hs
      split
      · rename_i sig callee args hi
        split
        · rename_i d hd
          simpa using hp.callInd b hb s hs sig callee args hi d hd
        · rfl
      · rfl
    · intro b hb
      split
      · rename_i c args et he
        exact absurd he (hp.noTryInd b hb c args et)
      · rfl

/-- **The validator is redundant on `preB`**: it accepts every legalisation of a function with
`preB f = true`. -/
theorem check_complete_of_preB {f g : Function} {cert : Cert} (hp : preB f = true)
    (h : function128Cert f = .ok (g, cert)) : check f g cert = true :=
  check_complete (preB_iff.1 hp) h

/-- **`checkW` is redundant on `preBW`**: it accepts every legalisation of a function with
`preBW f = true`. -/
theorem checkW_complete_of_preBW {f g : Function} {cert : Cert} (hp : preBW f = true)
    (h : function128Cert f = .ok (g, cert)) : checkW f g cert = true :=
  checkW_complete (preBW_iff.1 hp) h

/-- A function without `i128` is its own legalisation. -/
theorem function128Cert_of_not_mentions {f : Function} (h : mentions128 f = false) :
    function128Cert f = .ok (f, {}) := by
  simp [function128Cert, h]
  rfl

theorem legalize_of_not_mentions {f : Function} (h : mentions128 f = false) : legalize f = f := by
  simp [legalize, function128Cert_of_not_mentions h]

theorem legalize_of_ok {f g : Function} {cert : Cert} (h : function128Cert f = .ok (g, cert)) :
    legalize f = g := by
  simp [legalize, h]

/-- **The source domain of one function**: the pass is the identity, or `Pre` holds and the
pass succeeds (`legalize f` is its result). -/
theorem legalOkB_cases {f : Function} (h : legalOkB f = true) :
    (mentions128 f = false ∧ function128Cert f = .ok (f, {}) ∧ legalize f = f) ∨
    (Pre f ∧ ∃ cert, function128Cert f = .ok (legalize f, cert)) := by
  simp only [legalOkB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hok, hm | hp⟩ := h
  · exact .inl ⟨hm, function128Cert_of_not_mentions hm, legalize_of_not_mentions hm⟩
  · refine .inr ⟨preB_iff.1 hp, ?_⟩
    cases hc : function128Cert f with
    | error e => simp [hc, Except.toBool] at hok
    | ok gc => exact ⟨gc.2, by simp [legalize, hc]⟩

/-! ## Witnesses -/

namespace Witness

/-- `%add128(i128, i128) -> i128`: `v2 = iadd.i128 v0, v1; return v2`. -/
def add128 : Function where
  name := "add128"
  sig := { params := [{ ty := .i128 }, { ty := .i128 }], returns := [{ ty := .i128 }] }
  blocks := [{ id := 0, params := [(0, .i128), (1, .i128)],
               body := [{ results := [2], inst := .binary .iadd .i128 0 1 }], term := .ret [2] }]

/-- `add128` satisfies `Pre`, and its legalisation is accepted without running the
validator. -/
theorem add128_pre : Pre add128 := preB_iff.1 (by decide +kernel)

theorem add128_legal : ∃ g cert, function128Cert add128 = .ok (g, cert) ∧ check add128 g cert = true := by
  have ht : (function128Cert add128).toBool = true := by decide +kernel
  cases h : function128Cert add128 with
  | error e => rw [h] at ht; cases ht
  | ok r => exact ⟨r.1, r.2, rfl, check_complete add128_pre h⟩

theorem add128_legalOkB : legalOkB add128 = true := by decide +kernel

/-- `%stack128(i64 × 8, i128) -> i128`: `return v8`, the pair passed on the stack (`x0..x7`
used up): `Pre` holds and the legalisation, with the halves as the ninth and tenth `i64`
parameters (no pad: stack offset 0 is 16-aligned), is accepted. -/
def stack128 : Function where
  name := "stack128"
  sig := { params := (List.replicate 8 { ty := .i64 }) ++ [{ ty := .i128 }],
           returns := [{ ty := .i128 }] }
  blocks := [{ id := 0, params := ((List.range 8).map (·, .i64)) ++ [(8, .i128)],
               body := [], term := .ret [8] }]

theorem stack128_pre : Pre stack128 := preB_iff.1 (by decide +kernel)

theorem stack128_legal : ∃ g cert, function128Cert stack128 = .ok (g, cert) ∧
    g.sig.params = List.replicate 10 { ty := .i64 } ∧ check stack128 g cert = true := by
  have ht : ((function128Cert stack128).toOption.map (·.1.sig.params)) =
      some (List.replicate 10 { ty := .i64 }) := by decide +kernel
  cases h : function128Cert stack128 with
  | error e => rw [h] at ht; cases ht
  | ok r =>
    rw [h] at ht
    exact ⟨r.1, r.2, rfl, by simpa [Except.toOption] using ht, check_complete stack128_pre h⟩

/-- `%hole128(i64 × 7, i128, i64) -> i128`: `return v7` (`x7` placement: Cranelift passes the
pair on the stack and `v8` in `x7`): `Pre` holds and the legalisation, with `v8` as the eighth
`i64` parameter (`x7`) and the halves as the ninth and tenth (the stack), is accepted. -/
def hole128 : Function where
  name := "hole128"
  sig := { params := (List.replicate 7 { ty := .i64 }) ++ [{ ty := .i128 }, { ty := .i64 }],
           returns := [{ ty := .i128 }] }
  blocks := [{ id := 0, params := ((List.range 7).map (·, .i64)) ++ [(7, .i128), (8, .i64)],
               body := [], term := .ret [7] }]

theorem hole128_pre : Pre hole128 := preB_iff.1 (by decide +kernel)

theorem hole128_legal : ∃ g cert, function128Cert hole128 = .ok (g, cert) ∧
    g.sig.params = List.replicate 10 { ty := .i64 } ∧
    (g.blocks.head?.bind (·.params[7]?)) = some (8, .i64) ∧ check hole128 g cert = true := by
  have ht : ((function128Cert hole128).toOption.map
      fun r => (r.1.sig.params, r.1.blocks.head?.bind (·.params[7]?))) =
      some (List.replicate 10 { ty := .i64 }, some (8, .i64)) := by decide +kernel
  cases h : function128Cert hole128 with
  | error e => rw [h] at ht; cases ht
  | ok r =>
    rw [h] at ht
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
    exact ⟨r.1, r.2, rfl, ht.1, ht.2, check_complete hole128_pre h⟩

/-- `%saddof128(i128, i128) -> i128, i8`: `v2, v3 = sadd_overflow v0, v1; return v2, v3`:
`Pre` holds and the legalisation (the pure pattern `Pat.overflow .saddOverflow`) is accepted. -/
def saddof128 : Function where
  name := "saddof128"
  sig := { params := [{ ty := .i128 }, { ty := .i128 }],
           returns := [{ ty := .i128 }, { ty := .i8 }] }
  blocks := [{ id := 0, params := [(0, .i128), (1, .i128)],
               body := [{ results := [2, 3], inst := .overflow .saddOverflow .i128 0 1 }],
               term := .ret [2, 3] }]

theorem saddof128_pre : Pre saddof128 := preB_iff.1 (by decide +kernel)

theorem saddof128_legal : ∃ g cert, function128Cert saddof128 = .ok (g, cert) ∧
    check saddof128 g cert = true := by
  have ht : (function128Cert saddof128).toBool = true := by decide +kernel
  cases h : function128Cert saddof128 with
  | error e => rw [h] at ht; cases ht
  | ok r => exact ⟨r.1, r.2, rfl, check_complete saddof128_pre h⟩

def blk (body : List Stmt) (term : Terminator) : Block :=
  { id := 0, params := [(0, .i128), (1, .i128)], body, term }

/-- Not `Pre`: no `i128` (`mentions`; the pass is the identity, `legalOkB` holds). -/
def add64 : Function where
  name := "add64"
  sig := { params := [{ ty := .i64 }, { ty := .i64 }], returns := [{ ty := .i64 }] }
  blocks := [{ id := 0, params := [(0, .i64), (1, .i64)],
               body := [{ results := [2], inst := .binary .iadd .i64 0 1 }], term := .ret [2] }]

-- `mentions128 add64` evaluates `typeMapOf` (a `Std.HashMap`), which the kernel does not reduce
theorem add64_not_pre : ¬ Pre add64 := fun h => absurd (preB_iff.2 h) (by native_decide)
theorem add64_legalOkB : legalOkB add64 = true := by native_decide

/-- Not `Pre`: `v2` defined twice (`defs`). -/
def dupDef : Function := { add128 with blocks := [blk
  [{ results := [2], inst := .binary .iadd .i128 0 1 },
   { results := [2], inst := .binary .isub .i128 0 1 }] (.ret [2])] }

theorem dupDef_not_pre : ¬ Pre dupDef := fun h => absurd (preB_iff.2 h) (by decide +kernel)

/-- Not `Pre`: `v7` is read but never defined, above `maxValueId` (`ids`). -/
def bigId : Function := { add128 with blocks := [blk
  [{ results := [2], inst := .binary .iadd .i128 0 7 }] (.ret [2])] }

theorem bigId_not_pre : ¬ Pre bigId := fun h => absurd (preB_iff.2 h) (by decide +kernel)

/-- Not `Pre`: `v2 = iadd.i128 v0, v2` reads its own result (`noSelf`). -/
def selfRead : Function := { add128 with blocks := [blk
  [{ results := [2], inst := .binary .iadd .i128 0 2 }] (.ret [2])] }

theorem selfRead_not_pre : ¬ Pre selfRead := fun h => absurd (preB_iff.2 h) (by decide +kernel)

def sig128d : Signature := { params := [{ ty := .i128 }], returns := [{ ty := .i128 }] }

/-- Not `Pre`: a `call_indirect` with an `i128` signature (`callInd`). `PreW` holds and `checkW`
accepts the legalisation (`Plan.callInd128`: the call with the pair as two `i64` arguments and
results, at the expanded `sig0`). -/
def indI128 : Function := { add128 with sigDecls := [(0, sig128d)], blocks := [blk
  [{ results := [3], inst := .iconst .i64 0 },
   { results := [2], inst := .callIndirect 0 3 [0] }] (.ret [2])] }

theorem indI128_not_pre : ¬ Pre indI128 := fun h => absurd (preB_iff.2 h) (by decide +kernel)

theorem indI128_preW : PreW indI128 := preBW_iff.1 (by decide +kernel)

theorem indI128_legal : ∃ g cert, function128Cert indI128 = .ok (g, cert) ∧
    checkW indI128 g cert = true := by
  have ht : (function128Cert indI128).toBool = true := by decide +kernel
  cases h : function128Cert indI128 with
  | error e => rw [h] at ht; cases ht
  | ok r => exact ⟨r.1, r.2, rfl, checkW_complete indI128_preW h⟩

/-- Not `Pre`: a `try_call_indirect` (`noTryInd`). `PreW` holds and `checkW` accepts the
legalisation (the arguments, results and normal-return arguments split by the groups of the
`i128` call-site signature). -/
def tryInd : Function := { add128 with sigDecls := [(0, sig128d)], blocks := [blk
  [{ results := [3], inst := .iconst .i64 0 }]
  (.tryCallIndirect 3 [0] { sig := 0, normal := { block := 1, args := [.ret 0] } }),
  { id := 1, params := [(4, .i128)], term := .ret [4] }] }

theorem tryInd_not_pre : ¬ Pre tryInd := fun h => absurd (preB_iff.2 h) (by decide +kernel)

theorem tryInd_preW : PreW tryInd := preBW_iff.1 (by decide +kernel)

theorem tryInd_legal : ∃ g cert, function128Cert tryInd = .ok (g, cert) ∧
    checkW tryInd g cert = true := by
  have ht : (function128Cert tryInd).toBool = true := by decide +kernel
  cases h : function128Cert tryInd with
  | error e => rw [h] at ht; cases ht
  | ok r => exact ⟨r.1, r.2, rfl, checkW_complete tryInd_preW h⟩

end Witness

end Opt.Legal.Complete
