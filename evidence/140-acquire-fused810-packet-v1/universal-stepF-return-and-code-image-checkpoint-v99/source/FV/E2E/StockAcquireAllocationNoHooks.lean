import FV.E2E.StockAcquireAssignNoHooks

namespace Backend.Proof
open Backend E2E Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

theorem spAddrX16_no_hooks (off : Nat) : ∀ inst ∈ spAddrX16 off, NoHookInst inst := by
  intro inst member
  simp only [spAddrX16, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at member
  rcases member with (rfl | ⟨pair, _, rfl⟩) | rfl <;> trivial

theorem slotStoreAt_no_hooks (cls : RegClass) (reg : Reg) (off : Nat) :
    ∀ inst ∈ slotStoreAt cls reg off, NoHookInst inst := by
  unfold slotStoreAt
  split
  · intro inst member
    simp only [List.mem_singleton] at member
    subst inst
    cases cls <;> simp [slotStore,NoHookInst]
  · intro inst member
    rcases List.mem_append.mp member with member | member
    · exact spAddrX16_no_hooks off inst member
    · simp only [List.mem_singleton] at member
      subst inst
      cases cls <;> trivial

theorem slotLoadAt_no_hooks (cls : RegClass) (reg : Reg) (off : Nat) :
    ∀ inst ∈ slotLoadAt cls reg off, NoHookInst inst := by
  unfold slotLoadAt
  split
  · intro inst member
    simp only [List.mem_singleton] at member
    subst inst
    cases cls <;> simp [slotLoad,NoHookInst]
  · intro inst member
    rcases List.mem_append.mp member with member | member
    · exact spAddrX16_no_hooks off inst member
    · simp only [List.mem_singleton] at member
      subst inst
      cases cls <;> trivial

theorem moveInsts_no_hooks {frame : RAFrame} {src dst : Loc} {code : List AInst}
    (run : frame.moveInsts src dst = .ok code) : ∀ inst ∈ code, NoHookAInst inst := by
  unfold RAFrame.moveInsts at run
  repeat' split at run
  all_goals try simp only [bind, Except.bind, pure, Except.pure] at run
  all_goals try (cases run)
  all_goals repeat' split at run
  all_goals try simp only [pure, Except.pure, Except.ok.injEq] at run
  all_goals try subst code
  all_goals intro inst member
  all_goals try simp only [List.mem_nil_iff, List.mem_singleton, List.mem_map, List.mem_append] at member
  all_goals first
    | contradiction
    | (subst inst; trivial)
    | (obtain ⟨original, member, rfl⟩ := member
       change NoHookInst original
       first
       | exact slotStoreAt_no_hooks _ _ _ original member
       | exact slotLoadAt_no_hooks _ _ _ original member
       | (rcases member with member | member
          · exact slotStoreAt_no_hooks _ _ _ original member
          · exact slotLoadAt_no_hooks _ _ _ original member))

theorem itemCode_no_hooks {frame : RAFrame} {block : VBlock} {item : RItem} {code : List AInst}
    (run : itemCode frame block item = .ok code)
    (noHook : ∀ inst ∈ block.insts.toList, NoHookInst inst) :
    ∀ inst ∈ code, NoHookAInst inst := by
  cases item with
  | move src dst => exact moveInsts_no_hooks (by rwa [itemCode_move] at run)
  | op index allocs =>
    obtain ⟨registers, original, assigned, _, lookup, assignedRun, shape⟩ := itemCode_op run
    have assignedNoHook := assign_no_hooks (noHook original (by simpa using Array.mem_of_getElem? lookup)) assignedRun
    rcases shape with ⟨rfl, _, _⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · intro inst member; simp only [List.mem_singleton] at member; subst inst; exact assignedNoHook
    · simp
    · intro inst member; simp only [List.mem_singleton] at member; subst inst; trivial

theorem itemsCode_no_hooks {frame : RAFrame} {block : VBlock}
    (noHook : ∀ inst ∈ block.insts.toList, NoHookInst inst) :
    ∀ {items : List RItem} {code : List AInst},
      itemsCode frame block items = .ok code → ∀ inst ∈ code, NoHookAInst inst
  | [], code, run => by cases run; simp
  | item :: rest, code, run => by
    obtain ⟨first, tail, firstRun, tailRun, rfl⟩ := itemsCode_cons run
    intro inst member
    rcases List.mem_append.mp member with member | member
    · exact itemCode_no_hooks firstRun noHook inst member
    · exact itemsCode_no_hooks noHook tailRun inst member

end Backend.Proof
