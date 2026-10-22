import FV.E2E.SrcBounded
import FV.E2E.LinkArm

/-! # The source run enters only callees of the linked legalised program (A2/B1)

A whole-program run of a source program `P` in the source domain (`ProgCtx`) enters a function
`h` from an activation of `g` (`SrcBounded.EnterVia`): then `legalize h` is a callee
(`LinkSys.Callee`) of `legalize g` in any linked system of the legalised program `legalProg P`
with `P`'s link-time symbols (`callee_of_enter`). An indirect call keeps its call-site signature
(without `i128` in the source domain, `pre_indSite`) through the legalisation
(`checkW_callInd_sig`), so `legalize h` matches one of `legalize g`'s indirect-call signatures
(`indSig_legal`). -/

namespace E2E.SrcBounded
set_option autoImplicit false
open Clif Opt.Legal Opt.Legalize128 E2E.LegalProgram

theorem not_indFree_of_site {g : Function} {sig : Nat} (h : IndSite g sig) : ¬ IndFree g := by
  intro hf
  rcases h with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, callee, args, et, ht, -⟩
  · exact (hf B hB).1 st hst sig callee args hi
  · exact (hf B hB).2 callee args et ht

theorem mem_indSigs_stmt {f : Function} {B : Block} (hB : B ∈ f.blocks) {st : Stmt}
    (hst : st ∈ B.body) {sig : Nat} {callee : ValueId} {args : List ValueId}
    (hi : st.inst = .callIndirect sig callee args) {d : Signature}
    (hd : f.sigDecls.lookup sig = some d) : d ∈ Backend.indSigs f := by
  simp only [Backend.indSigs, List.mem_flatMap, List.mem_append, List.mem_filterMap]
  exact ⟨B, hB, .inl ⟨st, hst, by rw [hi]; exact hd⟩⟩

theorem mem_indSigs_term {f : Function} {B : Block} (hB : B ∈ f.blocks) {callee : ValueId}
    {args : List ValueId} {et : ExnTable} (ht : B.term = .tryCallIndirect callee args et)
    {d : Signature} (hd : f.sigDecls.lookup et.sig = some d) : d ∈ Backend.indSigs f := by
  simp only [Backend.indSigs, List.mem_flatMap, List.mem_append]
  exact ⟨B, hB, .inr (by rw [ht]; simp [hd])⟩

/-- **An accepted legalisation keeps every `call_indirect` call-site signature** (`checkW_callInd`
with the signature). -/
theorem checkW_callInd_sig {f g : Function} {cert : Cert} (hc : checkW f g cert = true)
    {B : Block} (hB : B ∈ f.blocks) {st : Stmt} (hst : st ∈ B.body) {sig : Nat} {callee : ValueId}
    {args : List ValueId} (hi : st.inst = .callIndirect sig callee args) :
    ∃ B' ∈ g.blocks, ∃ st' ∈ B'.body, ∃ callee' args', st'.inst = .callIndirect sig callee' args' := by
  have hG : Good ⟨f, g, cert⟩ := checkW_good hc
  obtain ⟨b, bs, b', bs', hf, hg, hl, hb, hz⟩ := hG.blocks
  simp only at hf hg
  rw [hf] at hB
  rcases List.mem_cons.1 hB with rfl | hB
  · simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ite_true] at hb
    obtain ⟨-, hok⟩ := hb
    split at hok
    · rename_i gs z rest hgs hbody'
      simp only [Bool.and_eq_true] at hok
      obtain ⟨st', hm, callee', args', hi'⟩ := codeOk_callInd hok.2 st hst sig callee args hi
      refine ⟨b', ?_, st', ?_, callee', args', hi'⟩
      · rw [hg]; exact List.mem_cons_self ..
      · rw [hbody']; exact List.mem_cons_of_mem _ hm
    · cases hok
  · obtain ⟨B', hB', hz'⟩ := mem_zip_of_mem hl hB
    have hok := hz B B' hz'
    simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true,
      ite_false] at hok
    obtain ⟨-, -, hcode⟩ := hok
    obtain ⟨st', hm, callee', args', hi'⟩ := codeOk_callInd hcode st hst sig callee args hi
    refine ⟨B', ?_, st', hm, callee', args', hi'⟩
    rw [hg]; exact List.mem_cons_of_mem _ hB'

theorem expandSigDecls_lookup : ∀ {ds ds' : List (Nat × Signature)}, expandSigDecls ds = .ok ds' →
    ∀ {i : Nat} {d : Signature}, ds.lookup i = some d →
      ∃ d', expandSig d = .ok d' ∧ ds'.lookup i = some d'
  | [], _, _, _, _, hl => by simp at hl
  | (j, s) :: ds, ds', h, i, d, hl => by
    simp only [expandSigDecls] at h
    obtain ⟨s', hs', h⟩ := Opt.Legal.Complete.except_bind_ok h
    obtain ⟨r, hr, h⟩ := Opt.Legal.Complete.except_bind_ok h
    cases h
    simp only [List.lookup] at hl ⊢
    by_cases hij : i = j
    · subst hij
      simp only [beq_self_eq_true, Option.some.injEq] at hl ⊢
      subst hl
      exact ⟨s', hs', rfl⟩
    · have hne : (i == j) = false := by simpa using hij
      rw [hne] at hl ⊢
      exact expandSigDecls_lookup hr hl

/-- **The legalised call site matches the legalised callee**: an indirect call of `g` at a
call-site signature `d` matching `h`'s (source domain) is, in `legalize g`, an indirect call at a
signature matching `legalize h`'s. -/
theorem indSig_legal {g h : Function} (hg : legalOkB g = true) (hh : legalOkB h = true)
    {sig : Nat} {d : Signature} (hs : IndSite g sig) (hd : g.sigDecls.lookup sig = some d)
    (hm : d.abiMatch h.sig = true) :
    ∃ s ∈ Backend.indSigs (legalize g), LinkSys.IndSigMatch s (legalize h) := by
  have hd128 : sig128 d = false := by
    rcases Opt.Legal.Complete.legalOkB_cases hg with ⟨hm0, -, -⟩ | ⟨hp, -⟩
    · exact (not_mentions hm0).2.2 _ (Opt.Legal.Complete.lookup_mem hd)
    · exact pre_indSite hp hs hd
  have hm' := Signature.abiMatch_eq_true.mp hm
  have hh128 : sig128 h.sig = false := sig128_of_tys hd128 hm'.1 hm'.2.2
  have hlh : (legalize h).sig = h.sig := by
    have := (legalFacts hh).sig
    rw [Opt.Legal.Complete.sigExp_plain hh128] at this
    exact (Option.some.inj this).symm
  refine ⟨d, ?_, show d.abiMatch (legalize h).sig = true by rw [hlh]; exact hm⟩
  rcases Opt.Legal.Complete.legalOkB_cases hg with ⟨-, -, hl⟩ | ⟨hp, cert, hc⟩
  · rw [hl]
    rcases hs with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, callee, args, et, ht, rfl⟩
    · exact mem_indSigs_stmt hB hst hi hd
    · exact mem_indSigs_term hB ht hd
  · rcases hs with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, callee, args, et, ht, -⟩
    · obtain ⟨B', hB', st', hst', callee', args', hi'⟩ :=
        checkW_callInd_sig (checkW_of_check (Opt.Legal.Complete.check_complete hp hc)) hB hst hi
      obtain ⟨es, ds, -, hds, -, hgd⟩ := function128Cert_spec hp.mentions hc
      obtain ⟨d', hd', hl'⟩ := expandSigDecls_lookup hds hd
      have : d' = d := by
        have h1 := Opt.Legal.Complete.sigExp_plain hd128
        simp only [sigExp, hd', Except.toOption] at h1
        exact Option.some.inj h1
      subst this
      exact mem_indSigs_stmt hB' hst' hi' (by rw [hgd]; exact hl')
    · exact absurd ht (hp.noTryInd B hB callee args et)

/-- **The source run enters only callees**: in a linked system `L` of the legalisation of a
source program `P` (source domain) with `P`'s link-time symbols, a function `h` the source run
enters from an activation of `g` (whose memory has those symbols at an indirect call) has
`legalize h` as a callee of `legalize g`. -/
theorem callee_of_enter {L : LinkSys} {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) (hLP : L.P = legalProg P) (hsy : L.syms = syms) {g h : Function}
    (hg : g ∈ P.funcs) {mem : Mem} (hv : EnterVia P g h mem)
    (hms : (∃ sig, IndSite g sig) → mem.symbols = syms) :
    L.Callee (legalize g) (legalize h) := by
  rcases hv with ⟨e, he, hpf⟩ | ⟨hh, sig, d, hs, hd, hm, a, ha⟩
  · obtain ⟨hn, hne, -⟩ := (legalFacts (hC.ok g hg)).names
    have hen : e.name ∈ (legalize g).externs.map (·.2.name) := by
      rw [hne, List.mem_append]
      left
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact List.mem_map_of_mem (f := (·.2.name)) he'
    obtain ⟨e', he', hee⟩ := List.mem_map.1 hen
    refine .inr (.inl ⟨e'.2, List.mem_map_of_mem (f := (·.2)) he', ?_⟩)
    rw [hLP, hee]
    exact hC.func?_some hpf
  · have hpf : P.func? h.name = some h := func?_of_mem hC.nd hh
    have hlname : (legalize h).name = h.name := (legalFacts (hC.ok h hh)).name
    have hlpf : L.P.func? (legalize h).name = some (legalize h) := by
      rw [hLP, hlname]; exact hC.func?_some hpf
    refine .inr (.inr ⟨(Program.func?_some hlpf).1, .inr ⟨(legalFacts (hC.ok g hg)).ind
      (not_indFree_of_site hs), ?_, fun h' hh' => ?_⟩⟩)
    · rw [hsy, hlname, ← hms ⟨sig, hs⟩, ha]; simp
    · rw [hlpf] at hh'
      cases hh'
      exact indSig_legal (hC.ok g hg) (hC.ok h hh) hs hd hm

end E2E.SrcBounded
