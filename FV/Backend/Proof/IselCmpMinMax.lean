import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.IselFamALUA

/-!
# Family C: integer `umin`/`smin`/`umax`/`smax` (1222/1224/1226/1228)

`output (lower_select ty (emit_icmp cc x y) x y)`: the comparison (`emit_icmp_ok`), then `cmp`
and `csel` (`lower_select_ok`, `condCode_csel`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ite_min_eq {w : Nat} {a b : BitVec w} {p q : Bool} (hpq : p = true → q = true)
    (he : q = true → p = false → a = b) : (if p then a else b) = (if q then a else b) := by
  cases p <;> cases q <;> simp_all
theorem minmax_sem (w : Nat) (a b : BitVec w) :
    (if Clif.Sem.intcc .ult a b then a else b) = Clif.Sem.binary .umin a b ∧
    (if Clif.Sem.intcc .slt a b then a else b) = Clif.Sem.binary .smin a b ∧
    (if Clif.Sem.intcc .ugt a b then a else b) = Clif.Sem.binary .umax a b ∧
    (if Clif.Sem.intcc .sgt a b then a else b) = Clif.Sem.binary .smax a b := by
  simp only [Clif.Sem.intcc, Clif.Sem.binary, Clif.Sem.umin, Clif.Sem.smin, Clif.Sem.umax, Clif.Sem.smax]
  refine ⟨ite_min_eq ?_ ?_, ite_min_eq ?_ ?_, ite_min_eq ?_ ?_, ite_min_eq ?_ ?_⟩ <;>
    simp only [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    intros <;> first | omega | (apply BitVec.eq_of_toNat_eq; omega) | (apply BitVec.eq_of_toInt_eq; omega)

theorem evalInst_binary_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.BinaryOp}
    {ty : Clif.Ty} {a b : Nat} {vals : List Clif.Val} (hs : op.isShift = false)
    (h : Clif.evalInst fr cm (.binary op ty a b) = .ok (vals, cm')) :
    ∃ u w, fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok w ∧
      vals = [⟨ty, Clif.Sem.binary op u w⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst, hs, Bool.false_eq_true, ↓reduceIte] at h
  cases ha : fr.getAs a ty with
  | trap c => rw [ha] at h; cases h
  | stuck m => rw [ha] at h; cases h
  | ok u =>
  cases hb : fr.getAs b ty with
  | trap c => rw [ha, hb] at h; cases h
  | stuck m => rw [ha, hb] at h; cases h
  | ok w =>
  rw [ha, hb] at h
  simp only [Clif.Res.ok_bind, Clif.Res.pure_eq] at h
  injection h with h
  injection h with h1 h2
  exact ⟨u, w, rfl, rfl, h1.symm, h2.symm⟩

section
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
/-- **Common tail of the min/max rules**, from the hypotheses `isel_inv` leaves. -/
theorem minmax_tail {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {cop : Clif.BinaryOp} {nm : String} {ko : Nat} {cc : Clif.IntCC}
    (hname : (variantNames 151)[ko]? = some nm) (hcop : binaryOpcode cop = some nm)
    (hsh : cop.isShift = false)
    (hsem : ∀ w (a b : BitVec w), (if Clif.Sem.intcc cc a b then a else b) = Clif.Sem.binary cop a b)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {st st' : LState} {tr : Array RuleId}
    (hvb : ValsBelow ctx st) {out v8 w3 w2 w1 c : V} {s4 s6 : LState × Array RuleId}
    {n1 n2 : Nat} (hn1 : 200 ≤ n1) (hn2 : 100 ≤ n2)
    (hout : externCtor ctx T.output [v8] s6.1 = .ok (out, st'))
    (hva : externExtract ctx T.value_array_2 w3 st = .ok [w2, w1])
    (hdd : V.data 152 2 [V.data 151 ko [], w3] = info.data)
    (h652 : ApplyInternal p (sem ctx) cfg n1 123 652 [.data 145 (ccIdx cc) [], w2, w1] (st, tr) c s4)
    (h659 : ApplyInternal p (sem ctx) cfg n2 22 659
      [.ty (info.resTys.head?.getD .invalid), c, w2, w1] s4 v8 s6) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      ∃ rss, out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, hfs⟩ := instData_binary_inv hname hcop hdat
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  rw [ext_value_array_2] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h659
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width] at h659
  have hC := emit_icmp_ok hp hco hR hctx (hn := hn1) hvb h652
  obtain ⟨mf, cond, rx, ry, hflag, hrx, hry, rfl, hs⟩ :=
    lower_select_ok hp hco (hn := hn2) (eTy_widths hety) hC.shape h659
  rw [ctor_output'] at hout
  obtain ⟨rfl, rfl⟩ := hout
  have hx := hvb x rx hrx
  have hy := hvb y ry hry
  rw [hctx.valueReg x rx hrx, hctx.valueReg y ry hry] at hs
  obtain ⟨hmono, ms, hf, hsm⟩ := condCode_csel hR hC hflag hx hy
  rw [hs]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨a, b, hxa, hyb, rfl, rfl⟩ := evalInst_binary_ok hsh ho
  have hxv := getAs_ok hxa
  have hyv := getAs_ok hyb
  obtain ⟨hu, hr⟩ := hsm fr ρ _ hh hdf ⟨ty, a, b, hxv, hyv, rfl⟩ (by simp [hxv]) (by simp [hyv])
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h, ← hsem]; exact vholds_select hety _ (hh _ _ hxv) (hh _ _ hyv)⟩

end

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem umin_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1222 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 _ h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  exact minmax_tail hp hR hMR (cop := .umin) (cc := .ult) rfl rfl rfl (fun w a b => (minmax_sem w a b).1)
    hctx hi hic hco hvb (by omega) (by omega) hout hva hdd h652 h659


set_option maxHeartbeats 8000000 in
include hp in
theorem smin_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1224 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 _ h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  exact minmax_tail hp hR hMR (cop := .smin) (cc := .slt) rfl rfl rfl (fun w a b => (minmax_sem w a b).2.1)
    hctx hi hic hco hvb (by omega) (by omega) hout hva hdd h652 h659


set_option maxHeartbeats 8000000 in
include hp in
theorem umax_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1226 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 _ h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  exact minmax_tail hp hR hMR (cop := .umax) (cc := .ugt) rfl rfl rfl (fun w a b => (minmax_sem w a b).2.2.1)
    hctx hi hic hco hvb (by omega) (by omega) hout hva hdd h652 h659


set_option maxHeartbeats 8000000 in
include hp in
theorem smax_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1228 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 _ h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_2 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  exact minmax_tail hp hR hMR (cop := .smax) (cc := .sgt) rfl rfl rfl (fun w a b => (minmax_sem w a b).2.2.2)
    hctx hi hic hco hvb (by omega) (by omega) hout hva hdd h652 h659

end Root

end Backend.Proof
