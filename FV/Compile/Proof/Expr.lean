import FV.Compile.Proof.Arith
import FV.Compile.Proof.RunEq
import FV.Compile.Proof.GenBk

/-!
# Expressions: `compileExpr` simulates `Expr.denote`

`expr_sim`: from a state at the generator position before `compileExpr c.fc env e`, the
machine reaches the position after it with the result values encoding `e.denote ρ`, without
changing any existing map object (`Ext`), or the run ends by resource exhaustion. The result's
map handles are fresh or come from variables `e` moved.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame State Mem Program Function Block Inst Terminator Outcome
  StepResult Signature ExtFunc FnRef BlockCall evalInst)
open DSL (Ty IntW CheckSt)

/-- Static facts about the function being run. -/
structure FnOK (c : Ctx) : Prop where
  ext : ExtIdx c.F
  rt : RtOK c.P
  eb : ∃ blk tid, c.EB blk tid

/-- Preconditions for running compiled code in context `Γ`. -/
structure XPre (c : Ctx) {Γ : List Ty} (ρ : DSL.Env Γ) (env : List (List ValueId))
    (vals : List (List Val)) (st : CheckSt) (H : Heap) (n : Nat) (s : State) : Prop where
  inv : c.Inv H s
  er : EnvRel H s.frame.regs Γ ρ env vals st
  ids : EnvIds env n
  n0 : c.n0 ≤ n
  len : st.length = Γ.length
  wf : ∀ t ∈ Γ, t.wf = true
  nd : (selHdl (alive st) Γ vals).Nodup

/-- The variables moved between `st` and `st'`. -/
def moved (st st' : CheckSt) (i : Nat) : Bool := alive st i && !alive st' i

/-- Progress of the machine within one activation: registers below `n` kept, invariant for
the new heap, which only extends the old one. -/
structure Prog (c : Ctx) (H : Heap) (s : State) (n : Nat) (H' : Heap) (s' : State) : Prop where
  agree : Agree s.frame.regs s'.frame.regs n
  inv : c.Inv H' s'
  ext : Ext H H'
  grows : Grows H H' s.mem.next
  mem : s.mem.next ≤ s'.mem.next

theorem Prog.trans {c : Ctx} {H H₁ H₂ : Heap} {s s₁ s₂ : State} {n n₁ : Nat}
    (h₁ : Prog c H s n H₁ s₁) (h₂ : Prog c H₁ s₁ n₁ H₂ s₂) (hn : n ≤ n₁) :
    Prog c H s n H₂ s₂ :=
  ⟨h₁.agree.trans h₂.agree hn, h₂.inv, h₁.ext.trans h₂.ext, h₁.grows.trans h₂.grows h₁.mem,
    Nat.le_trans h₁.mem h₂.mem⟩

theorem Prog.regs {c : Ctx} {H H' : Heap} {s s' : State} {n m : Nat}
    (h : Prog c H s n H' s') {fr : Frame} (hf : fr.func = s'.frame.func)
    (hs : fr.slots = s'.frame.slots) (ha : Agree s'.frame.regs fr.regs m) (hnm : n ≤ m)
    (hn0 : c.n0 ≤ m) : Prog c H s n H' { s' with frame := fr } :=
  ⟨h.agree.trans ha hnm, h.inv.frame hf hs ha hn0, h.ext, h.grows, h.mem⟩

theorem Prog.refl {c : Ctx} {H : Heap} {s : State} (n : Nat) (hI : c.Inv H s) :
    Prog c H s n H s := ⟨Agree.refl _ _, hI, Ext.refl _, Grows.refl _ _, Nat.le_refl _⟩

/-- Postcondition of an expression. -/
def XPost (c : Ctx) (Γ : List Ty) {t : Ty} (vals : List (List Val)) (st st' : CheckSt)
    (x : t.denote) (H : Heap) (s₀ : State) (n : Nat) (res : List ValueId × CG) (s : State) :
    Prop :=
  At c.F res.2 s.frame ∧ n ≤ res.2.nextVal ∧ (∀ y ∈ res.1, y < res.2.nextVal) ∧
    ∃ H' R, Prog c H s₀ n H' s ∧ RegsHas s.frame.regs res.1 R ∧ Enc H' t x R ∧ (hdl t R).Nodup ∧
      ∀ h ∈ hdl t R, H h = none ∨ h ∈ selHdl (moved st st') Γ vals

theorem XPre.next {c : Ctx} {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st st' : CheckSt} {H H' : Heap} {n n' : Nat} {s₀ s : State}
    {lim : Option Nat} (hX : XPre c ρ env vals st H n s₀) (hstep : ExprStep lim st st')
    (hp : Prog c H s₀ n H' s) (hn : n ≤ n') : XPre c ρ env vals st' H' n' s where
  inv := hp.inv
  er := ((hX.er.weaken hstep.al).agree hp.agree hX.ids).ext hp.ext
  ids := hX.ids.mono hn
  n0 := Nat.le_trans hX.n0 hn
  len := hstep.len.trans hX.len
  wf := hX.wf
  nd := hX.nd.sublist (selHdl_sublist hstep.al _ _)

theorem hdl_nonlinear : ∀ {t : Ty} (vs : List Val), t.linear = false → hdl t vs = []
  | .int _, _, _ | .bool, _, _ | .unit, _, _ => by simp [hdl]
  | .vec _ _, _, h | .map _ _, _, h => by simp [DSL.Ty.linear] at h
  | .prod a b, vs, h => by
    simp [DSL.Ty.linear] at h
    simp [hdl, hdl_nonlinear _ h.1, hdl_nonlinear _ h.2]

theorem hdl_int {w : IntW} (vs : List Val) : hdl (.int w) vs = [] := by simp [hdl]
theorem hdl_bool (vs : List Val) : hdl .bool vs = [] := by simp [hdl]

/-- A single fresh scalar result: the common tail of the arithmetic cases. -/
theorem XPost.scalar {c : Ctx} {Γ : List Ty} {t : Ty} {vals : List (List Val)}
    {st st' : CheckSt} {x : t.denote} {H H' : Heap} {s₀ s : State} {n : Nat}
    {res : List ValueId × CG} (v : Val)
    (hAt : At c.F res.2 s.frame) (hn : n ≤ res.2.nextVal) (hids : ∀ y ∈ res.1, y < res.2.nextVal)
    (hp : Prog c H s₀ n H' s) (hr : RegsHas s.frame.regs res.1 [v]) (he : Enc H' t x [v])
    (hh : hdl t [v] = []) : XPost c Γ vals st st' x H s₀ n res s :=
  ⟨hAt, hn, hids, H', [v], hp, hr, he, by rw [hh]; exact List.nodup_nil, by rw [hh]; simp⟩

theorem moved_left {lim : Option Nat} {st st₁ st₂ : CheckSt} (h : ExprStep lim st₁ st₂) (i : Nat)
    (hm : moved st st₁ i = true) : moved st st₂ i = true := by
  simp only [moved, Bool.and_eq_true, Bool.not_eq_true'] at hm ⊢
  refine ⟨hm.1, ?_⟩
  cases h2 : alive st₂ i
  · rfl
  · have := h.al i h2; rw [hm.2] at this; cases this

theorem moved_right {lim : Option Nat} {st st₁ st₂ : CheckSt} (h : ExprStep lim st st₁) (i : Nat)
    (hm : moved st₁ st₂ i = true) : moved st st₂ i = true := by
  simp only [moved, Bool.and_eq_true, Bool.not_eq_true'] at hm ⊢
  exact ⟨h.al i hm.1, hm.2⟩

theorem prov_left {Γ : List Ty} {vals : List (List Val)} {H : Heap} {lim : Option Nat}
    {st st₁ st₂ : CheckSt} (hs : ExprStep lim st₁ st₂) {hs' : List Nat}
    (h : ∀ x ∈ hs', H x = none ∨ x ∈ selHdl (moved st st₁) Γ vals) :
    ∀ x ∈ hs', H x = none ∨ x ∈ selHdl (moved st st₂) Γ vals := fun x hx =>
  (h x hx).imp id fun hm => (selHdl_sublist (moved_left hs) Γ vals).subset hm

theorem prov_right {Γ : List Ty} {vals : List (List Val)} {H H₁ : Heap} {lim : Option Nat}
    {st st₁ st₂ : CheckSt} (hs : ExprStep lim st st₁) (hx : Ext H H₁) {hs' : List Nat}
    (h : ∀ x ∈ hs', H₁ x = none ∨ x ∈ selHdl (moved st₁ st₂) Γ vals) :
    ∀ x ∈ hs', H x = none ∨ x ∈ selHdl (moved st st₂) Γ vals := fun x hm =>
  (h x hm).imp (fun h₁ => by
      cases hH : H x with
      | none => rfl
      | some p => rw [hx x p hH] at h₁; cases h₁)
    fun hm => (selHdl_sublist (moved_right hs) Γ vals).subset hm

/-- Results of two consecutive expressions have disjoint handles. -/
theorem hdl_disj2 {c : Ctx} {Γ : List Ty} {ρ : DSL.Env Γ} {env : List (List ValueId)}
    {vals : List (List Val)} {st st₁ st₂ : CheckSt} {H H₁ : Heap} {n : Nat} {s : State}
    {lim : Option Nat} (hX : XPre c ρ env vals st H n s) (hs₁ : ExprStep lim st st₁)
    {ta tb : Ty} {xa : ta.denote} {R₁ R₂ : List Val} (hE₁ : Enc H₁ ta xa R₁)
    (hv₁ : ∀ x ∈ hdl ta R₁, H x = none ∨ x ∈ selHdl (moved st st₁) Γ vals)
    (hv₂ : ∀ x ∈ hdl tb R₂, H₁ x = none ∨ x ∈ selHdl (moved st₁ st₂) Γ vals) :
    ∀ x, x ∈ hdl ta R₁ → x ∉ hdl tb R₂ := by
  intro x h₁ h₂
  rcases hv₂ x h₂ with hn | hm₂
  · exact hE₁.hdl_dom x h₁ hn
  · obtain ⟨j, tj, vj, hj₁, hj₂, hj₃, hj₄⟩ := mem_selHdl.1 hm₂
    simp only [moved, Bool.and_eq_true] at hj₃
    have hjs : alive st j = true := hs₁.al j hj₃.1
    have hsel : x ∈ selHdl (alive st) Γ vals := mem_selHdl.2 ⟨j, tj, vj, hj₁, hj₂, hjs, hj₄⟩
    rcases hv₁ x h₁ with hn | hm₁
    · exact selHdl_alive_dom hX.er x hsel hn
    · obtain ⟨i, ti, vi, hi₁, hi₂, hi₃, hi₄⟩ := mem_selHdl.1 hm₁
      simp only [moved, Bool.and_eq_true, Bool.not_eq_true'] at hi₃
      have := selHdl_disj hX.nd hi₁ hi₂ hj₁ hj₂ hi₃.1 hjs hi₄ hj₄
      subst this
      rw [hi₃.2] at hj₃; cases hj₃.1

theorem RegsHas.replicate {r : Regs} {xs : List ValueId} {vs : List Val} (h : RegsHas r xs vs) :
    ∀ n, RegsHas r (List.replicate n xs).flatten (List.replicate n vs).flatten
  | 0 => rfl
  | n + 1 => by simp only [List.replicate_succ, List.flatten_cons]; exact h.append (replicate h n)

theorem RegsHas.agree' {r r' : Regs} {n : Nat} {xs : List ValueId} {vs : List Val}
    (h : RegsHas r xs vs) (ha : Agree r r' n) (hx : ∀ x ∈ xs, x < n) : RegsHas r' xs vs :=
  h.agree ha hx

theorem moved_join_left {st a b : CheckSt} (hl : a.length = b.length) (i : Nat)
    (h : moved st a i = true) : moved st (DSL.Check.join a b) i = true := by
  simp only [moved, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  rw [alive_join hl, h.2]; exact ⟨h.1, rfl⟩

theorem moved_join_right {st a b : CheckSt} (hl : a.length = b.length) (i : Nat)
    (h : moved st b i = true) : moved st (DSL.Check.join a b) i = true := by
  simp only [moved, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  rw [alive_join hl, h.2]; simp [h.1]

theorem truthy_ofBool (b : Bool) : Clif.Sem.truthy (Val.ofBool b).bits = b := by
  cases b <;> rfl

/-- The simulation statement for one expression. -/
def SimE {Γ : List Ty} {t : Ty} (e : DSL.Expr Γ t) : Prop :=
  ∀ (c : Ctx), FnOK c → ∀ (ρ : DSL.Env Γ) (env : List (List ValueId)) (vals : List (List Val))
    (st st' : CheckSt) (lim : Option Nat) (H : Heap) (cg : CG) (s : State),
  XPre c ρ env vals st H cg.nextVal s → Good c.F ((compileExpr c.fc env e).run cg).2 →
  At c.F cg s.frame → e.chk lim st = .ok st' → (Expr.usesCtx e = true → c.fc.ctx.isSome) →
  Reach mapEnv c.P (XPost c Γ vals st st' (e.denote ρ) H s cg.nextVal
    ((compileExpr c.fc env e).run cg)) Exh s

theorem expr_sim {Γ : List Ty} {t : Ty} (e : DSL.Expr Γ t) : SimE e := by
  induction e with
  | @var τ v =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    obtain ⟨ha, hstep, hmove⟩ := use_ok hchk
    obtain ⟨hr, henc, hΓ, hv⟩ := hX.er.get v ha
    refine .here ⟨hAt, Nat.le_refl _, hX.ids.getD _, H, _, Prog.refl _ hX.inv, hr, henc,
      selHdl_nodup_one hX.nd hΓ hv ha, fun h hh => ?_⟩
    right
    cases hlin : τ.linear
    · rw [hdl_nonlinear _ hlin] at hh; simp at hh
    · refine mem_selHdl.2 ⟨v.idx, τ, _, hΓ, hv, ?_, hh⟩
      have := hmove hlin rfl (by rw [hX.len]; exact Var.idx_lt v)
      simp [moved, ha, this]
  | ilit w x =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk, Except.ok.injEq] at hchk
    rw [run_ilit] at hG ⊢
    refine reach_iconst hG hAt fun fr' hA hr hf hs => .here ?_
    exact XPost.scalar (intV w x) hA (by simp [iconstN_run]) (by simp [iconstN_run])
      ((Prog.refl _ hX.inv).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _))
        (Nat.le_refl _) hX.n0)
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_int _)
  | blit b =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    rw [run_blit] at hG ⊢
    refine reach_iconst hG hAt fun fr' hA hr hf hs => .here ?_
    exact XPost.scalar (Val.ofBool b) hA (by simp [iconstN_run]) (by simp [iconstN_run])
      ((Prog.refl _ hX.inv).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _))
        (Nat.le_refl _) hX.n0)
      (by rw [hr, ofBool_eq]; exact RegsHas.set_same _ _ _) rfl (hdl_bool _)
  | unit =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    rw [run_unit]
    exact .here ⟨hAt, Nat.le_refl _, by simp, H, [], Prog.refl _ hX.inv,
      rfl, rfl, by simp [hdl],
      by simp [hdl]⟩
  | @ibin w op a b iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨st₁, hc₁, hc₂⟩ := except_bind_ok.1 hchk
    rw [run_ibin] at hG ⊢
    have hG₂ := Bk.inst1_gg _ c.F _ hG
    have hG₁ := Bk.compileExpr c.fc env b c.F _ hG₂
    refine (iha c hF ρ env vals st st₁ lim H cg s hX hG₁ hAt hc₁
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    refine (ihb c hF ρ env vals st₁ st' lim H₁ _ s₁ (hX.next (Expr.chk_step a hc₁) hp₁ hn₁) hG₂
      hA₁ hc₂ (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, -, -⟩ := h₂
    simp only [Enc] at hE₁ hE₂; subst hE₁; subst hE₂
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    obtain ⟨xb, hxb, hvb⟩ := hr₂.single_inv
    have hva' : s₂.frame.regs xa = some (intV w (a.denote ρ)) := by
      rw [hp₂.agree xa (hid₁ xa (by simp [hxa]))]; exact hva
    refine reach_inst1 hG hA₂ (fun _ _ h => by cases h)
      (by rw [hxa, hxb]; exact eval_ibin _ _ op w hva' hvb) fun fr' hA hr hf hs => .here ?_
    have hn : cg.nextVal ≤ ((compileExpr c.fc env b).run ((compileExpr c.fc env a).run cg).2).2.nextVal :=
      Nat.le_trans hn₁ hn₂
    exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
      ((hp₁.trans hp₂ hn₁).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn
        (Nat.le_trans hX.n0 hn))
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_int _)
  | @icmp w op a b iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨st₁, hc₁, hc₂⟩ := except_bind_ok.1 hchk
    rw [run_icmp] at hG ⊢
    have hG₂ := Bk.inst1_gg _ c.F _ hG
    have hG₁ := Bk.compileExpr c.fc env b c.F _ hG₂
    refine (iha c hF ρ env vals st st₁ lim H cg s hX hG₁ hAt hc₁
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    refine (ihb c hF ρ env vals st₁ st' lim H₁ _ s₁ (hX.next (Expr.chk_step a hc₁) hp₁ hn₁) hG₂
      hA₁ hc₂ (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, -, -⟩ := h₂
    simp only [Enc] at hE₁ hE₂; subst hE₁; subst hE₂
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    obtain ⟨xb, hxb, hvb⟩ := hr₂.single_inv
    have hva' : s₂.frame.regs xa = some (intV w (a.denote ρ)) := by
      rw [hp₂.agree xa (hid₁ xa (by simp [hxa]))]; exact hva
    refine reach_inst1 hG hA₂ (fun _ _ h => by cases h)
      (by rw [hxa, hxb]; exact eval_icmp _ _ op w hva' hvb) fun fr' hA hr hf hs => .here ?_
    have hn : cg.nextVal ≤ ((compileExpr c.fc env b).run ((compileExpr c.fc env a).run cg).2).2.nextVal :=
      Nat.le_trans hn₁ hn₂
    exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
      ((hp₁.trans hp₂ hn₁).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn
        (Nat.le_trans hX.n0 hn))
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_bool _)
  | band a b iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨st₁, hc₁, hc₂⟩ := except_bind_ok.1 hchk
    rw [run_band] at hG ⊢
    have hG₂ := Bk.inst1_gg _ c.F _ hG
    have hG₁ := Bk.compileExpr c.fc env b c.F _ hG₂
    refine (iha c hF ρ env vals st st₁ lim H cg s hX hG₁ hAt hc₁
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    refine (ihb c hF ρ env vals st₁ st' lim H₁ _ s₁ (hX.next (Expr.chk_step a hc₁) hp₁ hn₁) hG₂
      hA₁ hc₂ (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, -, -⟩ := h₂
    simp only [Enc] at hE₁ hE₂; subst hE₁; subst hE₂
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    obtain ⟨xb, hxb, hvb⟩ := hr₂.single_inv
    have hva' : s₂.frame.regs xa = some (Val.ofBool (a.denote ρ)) := by
      rw [hp₂.agree xa (hid₁ xa (by simp [hxa]))]; exact hva
    refine reach_inst1 hG hA₂ (fun _ _ h => by cases h)
      (by rw [hxa, hxb]; exact eval_bool_bin _ _ .band (· && ·) band8 rfl hva' hvb) fun fr' hA hr hf hs => .here ?_
    have hn : cg.nextVal ≤ ((compileExpr c.fc env b).run ((compileExpr c.fc env a).run cg).2).2.nextVal :=
      Nat.le_trans hn₁ hn₂
    exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
      ((hp₁.trans hp₂ hn₁).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn
        (Nat.le_trans hX.n0 hn))
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_bool _)
  | bor a b iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨st₁, hc₁, hc₂⟩ := except_bind_ok.1 hchk
    rw [run_bor] at hG ⊢
    have hG₂ := Bk.inst1_gg _ c.F _ hG
    have hG₁ := Bk.compileExpr c.fc env b c.F _ hG₂
    refine (iha c hF ρ env vals st st₁ lim H cg s hX hG₁ hAt hc₁
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    refine (ihb c hF ρ env vals st₁ st' lim H₁ _ s₁ (hX.next (Expr.chk_step a hc₁) hp₁ hn₁) hG₂
      hA₁ hc₂ (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, -, -⟩ := h₂
    simp only [Enc] at hE₁ hE₂; subst hE₁; subst hE₂
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    obtain ⟨xb, hxb, hvb⟩ := hr₂.single_inv
    have hva' : s₂.frame.regs xa = some (Val.ofBool (a.denote ρ)) := by
      rw [hp₂.agree xa (hid₁ xa (by simp [hxa]))]; exact hva
    refine reach_inst1 hG hA₂ (fun _ _ h => by cases h)
      (by rw [hxa, hxb]; exact eval_bool_bin _ _ .bor (· || ·) bor8 rfl hva' hvb) fun fr' hA hr hf hs => .here ?_
    have hn : cg.nextVal ≤ ((compileExpr c.fc env b).run ((compileExpr c.fc env a).run cg).2).2.nextVal :=
      Nat.le_trans hn₁ hn₂
    exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
      ((hp₁.trans hp₂ hn₁).regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn
        (Nat.le_trans hX.n0 hn))
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_bool _)
  | @inot w a iha =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    rw [run_inot] at hG ⊢
    have hG₁ := Bk.inst1_gg _ c.F _ hG
    refine (iha c hF ρ env vals st st' lim H cg s hX hG₁ hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    simp only [Enc] at hE₁; subst hE₁
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    refine reach_inst1 hG hA₁ (fun _ _ h => by cases h)
      (by rw [hxa]; exact eval_inot _ _ w hva) fun fr' hA hr hf hs => .here ?_
    exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
      (hp₁.regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn₁
        (Nat.le_trans hX.n0 hn₁))
      (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_int _)
  | bnot a iha =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    rw [run_bnot] at hG ⊢
    have hG₂ := Bk.inst1_gg _ c.F _ hG
    have hG₁ := Bk.iconstN_gg _ _ c.F _ hG₂
    refine (iha c hF ρ env vals st st' lim H cg s hX hG₁ hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    simp only [Enc] at hE₁; subst hE₁
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    refine reach_iconst hG₂ hA₁ fun fr₂ hA₂ hr₂ hf₂ hs₂ => ?_
    have hva₂ : fr₂.regs xa = some (Val.ofBool (a.denote ρ)) := by
      rw [hr₂, Regs.set_other _ _ (Nat.ne_of_lt (hid₁ xa (by simp [hxa])))]; exact hva
    have hone : fr₂.regs ((compileExpr c.fc env a).run cg).2.nextVal = some (Val.ofBool true) := by
      rw [hr₂]; simp; rfl
    refine reach_inst1 (s := { s₁ with frame := fr₂ }) hG hA₂ (fun _ _ h => by cases h)
      (by rw [hxa]; exact eval_bool_bin _ _ .bxor (· ^^ ·) bxor8 rfl hva₂ hone)
      fun fr' hA hr hf hs => .here ?_
    have hn : cg.nextVal ≤ ((compileExpr c.fc env a).run cg).2.nextVal + 1 := by omega
    refine XPost.scalar _ hA (by simp [inst1_run, iconstN_run]; omega)
      (by simp [inst1_run, iconstN_run])
      (hp₁.regs (fr := fr') (by rw [hf, hf₂]) (by rw [hs, hs₂]) (by
        rw [hr, hr₂]
        exact (Agree.set _ (Nat.le_refl _)).trans (Agree.set _ (by simp [iconstN_run]))
          (Nat.le_refl _)) hn₁ (Nat.le_trans hX.n0 hn₁))
      (by rw [hr]; simp only [iconstN_run]; exact RegsHas.set_same _ _ _) ?_ (hdl_bool _)
    simp [Enc, DSL.Expr.denote]
  | @cast w op w' a iha =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨_, hok, hchk⟩ := except_bind_ok.1 hchk
    have hcast := need_ok.1 hok
    rw [run_cast] at hG ⊢
    have hG₁ : Good c.F ((compileExpr c.fc env a).run cg).2 := by
      split at hG
      · exact Bk.inst1_gg _ c.F _ hG
      · split at hG
        · exact Bk.inst1_gg _ c.F _ hG
        · exact hG
    refine (iha c hF ρ env vals st st' lim H cg s hX hG₁ hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    simp only [Enc] at hE₁; subst hE₁
    obtain ⟨xa, hxa, hva⟩ := hr₁.single_inv
    split
    · rename_i hlt
      simp only [hlt, ↓reduceIte] at hG
      have hden : DSL.Cast.denote op w'.bits (a.denote ρ) = (a.denote ρ).setWidth w'.bits := by
        cases op
        · rfl
        · simp [DSL.Check.castOk] at hcast; omega
        · rfl
      refine reach_inst1 hG hA₁ (fun _ _ h => by cases h)
        (by rw [hxa]; exact eval_ireduce _ _ hva hlt) fun fr' hA hr hf hs => .here ?_
      refine XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
        (hp₁.regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn₁
          (Nat.le_trans hX.n0 hn₁))
        (by rw [hr]; exact RegsHas.set_same _ _ _) ?_ (hdl_int _)
      simp only [Enc, DSL.Expr.denote, hden]
    · rename_i hge
      simp only [hge, ↓reduceIte] at hG
      split
      · rename_i hlt
        simp only [hlt, ↓reduceIte] at hG
        by_cases hsx : op = .sext
        · subst hsx
          simp only [↓reduceIte] at hG ⊢
          refine reach_inst1 hG hA₁ (fun _ _ h => by cases h)
            (by rw [hxa]; exact eval_sextend _ _ hva hlt) fun fr' hA hr hf hs => .here ?_
          exact XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
            (hp₁.regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn₁
              (Nat.le_trans hX.n0 hn₁))
            (by rw [hr]; exact RegsHas.set_same _ _ _) rfl (hdl_int _)
        · simp only [hsx, ↓reduceIte] at hG ⊢
          have hden : DSL.Cast.denote op w'.bits (a.denote ρ) = (a.denote ρ).setWidth w'.bits := by
            cases op
            · rfl
            · exact absurd rfl hsx
            · rfl
          refine reach_inst1 hG hA₁ (fun _ _ h => by cases h)
            (by rw [hxa]; exact eval_uextend _ _ hva hlt) fun fr' hA hr hf hs => .here ?_
          refine XPost.scalar _ hA (by simp [inst1_run]; omega) (by simp [inst1_run])
            (hp₁.regs hf hs (by rw [hr]; exact Agree.set _ (Nat.le_refl _)) hn₁
              (Nat.le_trans hX.n0 hn₁))
            (by rw [hr]; exact RegsHas.set_same _ _ _) ?_ (hdl_int _)
          simp only [Enc, DSL.Expr.denote, hden]
      · rename_i hle
        have hw : w = w' := intW_eq_of_bits (by omega)
        subst hw
        refine .here (XPost.scalar _ hA₁ hn₁ (by simp [hxa] at hid₁ ⊢; exact hid₁) hp₁
          (by rw [hxa]; exact RegsHas.single hva) ?_ (hdl_int _))
        cases op <;> simp [Enc, DSL.Expr.denote, DSL.Cast.denote, DSL.Ops.zext, DSL.Ops.sext,
          DSL.Ops.trunc]
  | @pair ta tb a b iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨st₁, hc₁, hc₂⟩ := except_bind_ok.1 hchk
    have hs₁ := Expr.chk_step a hc₁
    have hs₂ := Expr.chk_step b hc₂
    rw [run_pair] at hG ⊢
    have hG₁ := Bk.compileExpr c.fc env b c.F _ hG
    refine (iha c hF ρ env vals st st₁ lim H cg s hX hG₁ hAt hc₁
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, hnd₁, hv₁⟩ := h₁
    refine (ihb c hF ρ env vals st₁ st' lim H₁ _ s₁ (hX.next hs₁ hp₁ hn₁) hG
      hA₁ hc₂ (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, hnd₂, hv₂⟩ := h₂
    have hl₁ := hE₁.length
    refine .here ⟨hA₂, Nat.le_trans hn₁ hn₂, fun y hy => ?_, H₂, R₁ ++ R₂, hp₁.trans hp₂ hn₁,
      (hr₁.agree hp₂.agree hid₁).append hr₂, ⟨R₁, R₂, rfl, hE₁.ext hp₂.ext, hE₂⟩, ?_, ?_⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact Nat.lt_of_lt_of_le (hid₁ y hy) hn₂
      · exact hid₂ y hy
    · rw [Enc.hdl_prod hl₁]
      exact List.nodup_append.2 ⟨hnd₁, hnd₂, fun x h₁ y h₂ he =>
        hdl_disj2 hX hs₁ hE₁ hv₁ hv₂ x h₁ (he ▸ h₂)⟩
    · rw [Enc.hdl_prod hl₁]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact prov_left hs₂ hv₁ x hx
      · exact prov_right hs₁ hp₁.ext hv₂ x hx
  | @fst ta tb p ih =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    rw [run_fst] at hG ⊢
    refine (ih c hF ρ env vals st st' lim H cg s hX hG hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R, hp₁, hr₁, hE₁, hnd₁, hv₁⟩ := h₁
    obtain ⟨v₁, v₂, rfl, hE₁₁, hE₁₂⟩ := hE₁
    have hl := hE₁₁.length
    have htake : (v₁ ++ v₂).take (flat ta).length = v₁ := by rw [← hl]; simp
    rw [Enc.hdl_prod hl] at hnd₁ hv₁
    refine .here ⟨hA₁, hn₁, fun y hy => hid₁ y (List.mem_of_mem_take hy), H₁, v₁, hp₁,
      by have := hr₁.take (flat ta).length; rwa [htake] at this, hE₁₁,
      (List.nodup_append.1 hnd₁).1, fun x hx => hv₁ x (List.mem_append_left _ hx)⟩
  | @snd ta tb p ih =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    rw [run_snd] at hG ⊢
    refine (ih c hF ρ env vals st st' lim H cg s hX hG hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R, hp₁, hr₁, hE₁, hnd₁, hv₁⟩ := h₁
    obtain ⟨v₁, v₂, rfl, hE₁₁, hE₁₂⟩ := hE₁
    have hl := hE₁₁.length
    have hdrop : (v₁ ++ v₂).drop (flat ta).length = v₂ := by rw [← hl]; simp
    rw [Enc.hdl_prod hl] at hnd₁ hv₁
    refine .here ⟨hA₁, hn₁, fun y hy => hid₁ y (List.mem_of_mem_drop hy), H₁, v₂, hp₁,
      by have := hr₁.drop (flat ta).length; rwa [hdrop] at this, hE₁₂,
      (List.nodup_append.1 hnd₁).2.1, fun x hx => hv₁ x (List.mem_append_right _ hx)⟩
  | @vrepl tx n x ih =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    rw [run_vrepl] at hG ⊢
    refine (ih c hF ρ env vals st st' lim H cg s hX hG hAt hchk
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R, hp₁, hr₁, hE₁, hnd₁, hv₁⟩ := h₁
    refine .here ⟨hA₁, hn₁, fun y hy => ?_, H₁, (List.replicate n R).flatten, hp₁,
      hr₁.replicate n, ⟨List.replicate n R, by simp, rfl, fun i hi => ?_⟩, by simp [hdl],
      by simp [hdl]⟩
    · simp only [List.mem_flatten, List.mem_replicate] at hy
      obtain ⟨l, ⟨-, rfl⟩, hy⟩ := hy
      exact hid₁ y hy
    · simp only [DSL.Expr.denote, Vector.getElem_replicate]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp [hi, hE₁]
  | @cond τ cnd a b ihc iha ihb =>
    intro c hF ρ env vals st st' lim H cg s hX hG hAt hchk hctx
    simp only [DSL.Expr.chk] at hchk
    obtain ⟨stc, hcc, r₁⟩ := except_bind_ok.1 hchk
    obtain ⟨st₁, hca, r₂⟩ := except_bind_ok.1 r₁
    obtain ⟨st₂, hcb, r₃⟩ := except_bind_ok.1 r₂
    simp only [pure, Except.pure, Except.ok.injEq] at r₃; subst r₃
    have hsc := Expr.chk_step cnd hcc
    have hsa := Expr.chk_step a hca
    have hsb := Expr.chk_step b hcb
    have hl : st₁.length = st₂.length := hsa.len.trans hsb.len.symm
    rw [run_cond] at hG ⊢
    have hGb := Bk.selectVals_gg _ _ _ _ c.F _ hG
    have hGa := Bk.compileExpr c.fc env b c.F _ hGb
    have hGc := Bk.compileExpr c.fc env a c.F _ hGa
    refine (ihc c hF ρ env vals st stc lim H cg s hX hGc hAt hcc
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₁ h₁ => ?_
    obtain ⟨hA₁, hn₁, hid₁, H₁, R₁, hp₁, hr₁, hE₁, -, -⟩ := h₁
    simp only [Enc] at hE₁; subst hE₁
    obtain ⟨xc, hxc, hvc⟩ := hr₁.single_inv
    have hX₁ := hX.next hsc hp₁ hn₁
    refine (iha c hF ρ env vals stc st₁ lim H₁ _ s₁ hX₁ hGa hA₁ hca
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₂ h₂ => ?_
    obtain ⟨hA₂, hn₂, hid₂, H₂, R₂, hp₂, hr₂, hE₂, hnd₂, hv₂⟩ := h₂
    have hX₂ := hX₁.next (ExprStep.refl lim stc) hp₂ hn₂
    refine (ihb c hF ρ env vals stc st₂ lim H₂ _ s₂ hX₂ hGb hA₂ hcb
      (fun h => hctx (by simp [Expr.usesCtx, h]))).bind fun s₃ h₃ => ?_
    obtain ⟨hA₃, hn₃, hid₃, H₃, R₃, hp₃, hr₃, hE₃, hnd₃, hv₃⟩ := h₃
    have hxlt : xc < ((compileExpr c.fc env cnd).run cg).2.nextVal := hid₁ xc (by simp [hxc])
    have hvc' : s₃.frame.regs xc = some (Val.ofBool (cnd.denote ρ)) := by
      rw [hp₃.agree xc (Nat.lt_of_lt_of_le hxlt hn₂), hp₂.agree xc hxlt]; exact hvc
    refine reach_selectVals hG hA₃ (by rw [hxc]; exact hvc') (hr₂.agree hp₃.agree hid₂) hr₃
      hE₂.tys hE₃.tys fun fr' hA hr ha hf hs => .here ?_
    rw [truthy_ofBool] at hr
    have hp := (hp₁.trans hp₂ hn₁).trans hp₃ (Nat.le_trans hn₁ hn₂)
    have hn : cg.nextVal ≤ ((compileExpr c.fc env b).run
        ((compileExpr c.fc env a).run ((compileExpr c.fc env cnd).run cg).2).2).2.nextVal :=
      Nat.le_trans (Nat.le_trans hn₁ hn₂) hn₃
    have hsel := freshFor_run (flat τ)
    refine ⟨hA, ?_, ?_, H₃, _, hp.regs hf hs ha hn (Nat.le_trans hX.n0 hn), hr, ?_, ?_, ?_⟩
    · simp only [selectVals, bind_run, newBlock_run, freshFor_run, terminate_run, switchTo_run,
        pure_run]; omega
    · simp only [selectVals, bind_run, newBlock_run, freshFor_run, terminate_run, switchTo_run,
        pure_run]
      intro y hy; exact (List.mem_range'_1.1 hy).2
    · simp only [DSL.Expr.denote]
      split
      · exact hE₂.ext hp₃.ext
      · exact hE₃
    · split
      · exact hnd₂
      · exact hnd₃
    · split
      · intro x hx
        exact (prov_right hsc hp₁.ext hv₂ x hx).imp id fun hm =>
          (selHdl_sublist (moved_join_left hl) Γ vals).subset hm
      · intro x hx
        exact (prov_right hsc (hp₁.ext.trans hp₂.ext) hv₃ x hx).imp id fun hm =>
          (selHdl_sublist (moved_join_right hl) Γ vals).subset hm
  | _ => sorry

end Compile.Proof
