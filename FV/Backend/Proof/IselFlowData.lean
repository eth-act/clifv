import FV.Backend.Proof.IselFlowExt

/-!
# The atoms of the instruction data the driver builds

`instData`, `termData` and `tryCallData` build `InstructionData` values holding no register,
no instruction index and no `ElfTlsGetAddr` data; the CLIF values of a statement's data are
its operands (`instData_ok`).
-/

namespace Backend.Proof.Flow

open Backend Isle Isle.Aarch64

/-- Data without registers, instructions and `ElfTlsGetAddr`, whose values satisfy `P`. -/
def DataOk (P : Nat → Prop) (d : V) : Prop :=
  d.regsIn = [] ∧ d.instsIn = [] ∧ d.tlsIn = false ∧ ∀ n ∈ d.valsIn, P n

/-- `DataOk` of every value of a list. -/
def DataOkL (P : Nat → Prop) (fs : List V) : Prop := ∀ f ∈ fs, DataOk P f

theorem dataOkL_nil {P : Nat → Prop} : DataOkL P [] := fun _ h => by cases h

theorem dataOkL_cons {P : Nat → Prop} {f : V} {fs : List V} (h1 : DataOk P f) (h2 : DataOkL P fs) :
    DataOkL P (f :: fs) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact h1
  · exact h2 g hg

theorem dataOkL_regs {P : Nat → Prop} : ∀ {fs : List V}, DataOkL P fs → regsInL fs = []
  | [], _ => rfl
  | f :: fs, h => by
    simp only [regsInL_cons, List.append_eq_nil_iff]
    exact ⟨(h f List.mem_cons_self).1, dataOkL_regs fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem dataOkL_insts {P : Nat → Prop} : ∀ {fs : List V}, DataOkL P fs → instsInL fs = []
  | [], _ => rfl
  | f :: fs, h => by
    simp only [instsInL_cons, List.append_eq_nil_iff]
    exact ⟨(h f List.mem_cons_self).2.1, dataOkL_insts fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem dataOkL_tls {P : Nat → Prop} : ∀ {fs : List V}, DataOkL P fs → tlsInL fs = false
  | [], _ => rfl
  | f :: fs, h => by
    simp only [tlsInL_cons, Bool.or_eq_false_iff]
    exact ⟨(h f List.mem_cons_self).2.2.1, dataOkL_tls fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem dataOkL_vals {P : Nat → Prop} : ∀ {fs : List V}, DataOkL P fs → ∀ n ∈ valsInL fs, P n
  | [], _ => fun _ h => by cases h
  | f :: fs, h => by
    intro n hn
    simp only [valsInL_cons, List.mem_append] at hn
    rcases hn with hn | hn
    · exact (h f List.mem_cons_self).2.2.2 n hn
    · exact dataOkL_vals (fun g hg => h g (List.mem_cons_of_mem _ hg)) n hn

theorem dataOk_data {P : Nat → Prop} {ty : TypeId} {k : Nat} {fs : List V} (hty : ty ≠ tyMInst)
    (h : DataOkL P fs) : DataOk P (.data ty k fs) := by
  refine ⟨by simp [V.regsIn, dataOkL_regs h], by simp [V.instsIn, dataOkL_insts h], ?_,
    fun n hn => dataOkL_vals h n (by simpa [V.valsIn] using hn)⟩
  simp [V.tlsIn, dataOkL_tls h, hty]

theorem dataOk_mkVariant {P : Nat → Prop} {ty : TypeId} {name : String} {fs : List V}
    (hty : ty ≠ tyMInst) (h : DataOkL P fs) : DataOk P (mkVariant ty name fs) := by
  unfold mkVariant
  split
  · exact dataOk_data hty h
  · exact ⟨rfl, rfl, rfl, fun n hn => by simp [V.valsIn, opVals] at hn⟩

theorem dataOk_int {P : Nat → Prop} {i : Int} : DataOk P (.int i) :=
  ⟨rfl, rfl, rfl, fun n hn => by simp [V.valsIn] at hn⟩

theorem dataOk_value {P : Nat → Prop} {x : Nat} (h : P x) : DataOk P (.value x) :=
  ⟨rfl, rfl, rfl, fun n hn => by simp [V.valsIn] at hn; exact hn ▸ h⟩

theorem dataOk_values {P : Nat → Prop} {xs : List Nat} (h : ∀ x ∈ xs, P x) : DataOk P (.values xs) :=
  ⟨rfl, rfl, rfl, fun n hn => h n (by simpa [V.valsIn] using hn)⟩

theorem dataOk_op {P : Nat → Prop} {o : Opnd} (h1 : opRegs o = []) (h2 : opVals o = []) :
    DataOk P (.op o) :=
  ⟨by simp [V.regsIn, h1], rfl, rfl, fun n hn => by simp [V.valsIn, h2] at hn⟩

theorem dataOk_blockCalls {P : Nat → Prop} {bs : List Nat} : DataOk P (.blockCalls bs) :=
  ⟨rfl, rfl, rfl, fun n hn => by simp [V.valsIn] at hn⟩

/-- Build `DataOk` of an `instDataV` term. -/
macro "data_ok" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply dataOk_mkVariant (by decide)
    | with_reducible exact dataOkL_nil
    | with_reducible apply dataOkL_cons
    | with_reducible exact dataOk_int
    | with_reducible exact dataOk_blockCalls
    | with_reducible exact dataOk_op rfl rfl
    | with_reducible apply dataOk_value
    | with_reducible apply dataOk_values
  all_goals first
    | trivial
    | (intro x hx; simp_all [Driver.instArgs])
    | simp [Driver.instArgs]))

set_option maxRecDepth 20000 in
/-- **The data of a statement**: its values are the instruction's operands. -/
theorem instData_ok {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    DataOk (· ∈ Driver.instArgs c) d := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       data_ok)

/-- **The data of a terminator** (`termData`). -/
theorem termData_ok {t : Clif.Terminator} {d : V} (h : termData t = .ok d) :
    DataOk (fun _ => True) d := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       data_ok)

set_option maxRecDepth 20000 in
/-- **The data of a `try_call`** (`tryCallData`). -/
theorem tryCallData_ok {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : DataOk (fun _ => True) d := by
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           data_ok)

end Backend.Proof.Flow
