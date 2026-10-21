import FV.Backend.Proof.StockUnchangedHelper
import FV.Backend.Proof.IselFamAluBPopcnt
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

def helperScope : List Nat := [175, 201, 235, 316, 363, 371, 395, 409, 410, 414, 469, 473, 524, 1893, 1896, 1911, 1914, 1915, 2034, 2135, 2165, 2200]

theorem helpers_unchanged {p : Program} (hp : Data p) :
    ∀ t term,t ∈ helperScope → termOf p t = .ok term → term.id ∉ revisedCtors := by
  intro t term member lookup
  simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hp.t175] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t201] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t235] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t316] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t363] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t371] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t395] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t409] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t410] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t414] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t469] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t473] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t524] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t1893] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t1896] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t1911] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t1914] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t1915] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t2034] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t2135] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t2165] at lookup
    cases lookup
    decide +kernel
  · rw [hp.t2200] at lookup
    cases lookup
    decide +kernel

theorem helpers_closed {p : Program} (hp : Data p) :
    ∀ t term,t ∈ helperScope → termOf p t = .ok term →
      ∀ flags ex,term.kind = .decl flags (some .internal) ex →
        ∀ r ∈ p.rulesOf t,RuleScoped (fun k => k ∈ helperScope) r := by
  intro t term member lookup flags ex kind r recorded
  simp only [helperScope,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hp.t175] at lookup
    cases lookup
    cases kind
  · rw [hp.t201] at lookup
    cases lookup
    cases kind
  · rw [hp.t235] at lookup
    cases lookup
    cases kind
  · rw [hp.t316] at lookup
    cases lookup
    cases kind
  · rw [hp.t363] at lookup
    cases lookup
    rw [hp.r363] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2552]
  · rw [hp.t371] at lookup
    cases lookup
    rw [hp.r371] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2612]
  · rw [hp.t395] at lookup
    cases lookup
    rw [hp.r395] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2802]
  · rw [hp.t409] at lookup
    cases lookup
    rw [hp.r409] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2930]
  · rw [hp.t410] at lookup
    cases lookup
    rw [hp.r410] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    rcases recorded with rfl | rfl
    all_goals simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2938,rule_inst_2941]
  · rw [hp.t414] at lookup
    cases lookup
    rw [hp.r414] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_2970]
  · rw [hp.t469] at lookup
    cases lookup
    rw [hp.r469] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_3290]
  · rw [hp.t473] at lookup
    cases lookup
    rw [hp.r473] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_3311]
  · rw [hp.t524] at lookup
    cases lookup
    rw [hp.r524] at recorded
    simp only [List.mem_cons,List.not_mem_nil,or_false] at recorded
    subst r
    simp [RuleScoped,IfLetsScoped,ExprScoped,exprCalls,bindCalls,argCalls,helperScope,rule_inst_3545]
  · rw [hp.t1893] at lookup
    cases lookup
    cases kind
  · rw [hp.t1896] at lookup
    cases lookup
    cases kind
  · rw [hp.t1911] at lookup
    cases lookup
    cases kind
  · rw [hp.t1914] at lookup
    cases lookup
    cases kind
  · rw [hp.t1915] at lookup
    cases lookup
    cases kind
  · rw [hp.t2034] at lookup
    cases lookup
    cases kind
  · rw [hp.t2135] at lookup
    cases lookup
    cases kind
  · rw [hp.t2165] at lookup
    cases lookup
    cases kind
  · rw [hp.t2200] at lookup
    cases lookup
    cases kind
end Backend.Stock.Proof.Popcount
